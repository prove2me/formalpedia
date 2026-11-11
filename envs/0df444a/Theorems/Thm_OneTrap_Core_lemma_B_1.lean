-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_1
-- name    : OneTrap.Core.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:46:55.922325+00:00
-- url     : https://prove2.me/theorems/c3f37054-846e-4676-abb4-aa75e8772d0c
-- title:
--   Lemma B.1 — the principal-favored Bellman recursion (17): finiteness, measurability, the recursion, $P(A,0,0)=V_P(w\mid A)$ and a deterministic dynamically consistent maximizer
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$ and a finite technology $A$. At a state $(R,x,h)$ let $U(R,x,h)$ be the agent's maximum expected terminal wage minus the costs of boxes opened after the state, and $P(R,x,h)$ the maximum expected terminal residual among the policies attaining it. These values are finite, measurable, and satisfy
--   $$u_{\mathrm{stop}}=x,\ \ p_{\mathrm{stop}}=h,\ \ u_i=-c_i+\mathbb E[U(R\setminus\{i\},M_i,\widehat H_i)],\ \ p_i=\mathbb E[P(R\setminus\{i\},M_i,\widehat H_i)],$$
--   $$U(R,x,h)=\max_{j\in\{\mathrm{stop}\}\cup R}u_j,\qquad P(R,x,h)=\max_{j:\,u_j=U(R,x,h)}p_j .\tag{17}$$
--   At the initial state $P(A,0,0)=V_P(w\mid A)$, and a deterministic, dynamically consistent maximizer exists.
--
--   Differences from the source:
--   - encoding: U(R, x, h) and P(R, x, h): the agent's optimal value from the state and the best principal value among the policies attaining it → `Ubell`/`Pbell`: the optimal values of the search problem whose openable boxes are R and whose only initially available outcome is (x, h) (agent value as a supremum over policies, principal value as `pfValue`); reason: stopping yields exactly (x, h), as u_stop = x and p_stop = h in (17); earlier outcomes are lexicographically below the incumbent and the remaining outputs are independent of the past
--   - generalization: states (R, x, h) that arise in the search: x the highest observed wage, h the largest residual at wage x (so (x, h) ≥lex (0, 0)) → every finite R ⊆ A and every real x and h; reason: the continuation problem and the argument are defined for any incumbent pair; at the states of the source this is the source's statement
--   - encoding: a policy assigns to every history (distinct actions with observed outputs) a probability distribution over taking an unopened action or stopping and submitting the null output or an observed output, Borel in the observed outputs → `Policy`: a rule of the opened set S, the outputs y (pre-sampled from the product law) and one seed u uniform on [0, 1] that reads y only on S, is measurable, opens only unopened boxes and submits only available outcomes; reason: the order in which S was opened is itself a function of the rule, y on S and u, and one uniform seed generates independent randomizations for every step (and conversely), so the laws of (opened set, submitted output) are the same
--   - encoding: expected payoffs U_A, P_A in the extended reals (Appendix A) → `eexp`: lower Lebesgue integral of the positive part minus that of the negative part, in EReal; reason: the convention of Appendix A; never the Bochner integral; ⊤ − ⊤ (= ⊥ in EReal) does not arise for these payoffs because the agent payoff is bounded below and the principal payoff above by integrable variables
--   - reading: "these values are finite and measurable" → `≠ ⊥ ∧ ≠ ⊤` for every R, x, h, and `Measurable` as maps (x, h) ↦ U(R, x, h), P(R, x, h) into EReal for each R; reason: the parameters of the values are the incumbent pair; R ranges over a finite set
--   - encoding: max over j ∈ {stop} ∪ R and over j with u_j = U(R, x, h) → `max x (R.sup u)` and `max (if x = U then h else ⊥) (R.sup fun i => if u_i = U then p_i else ⊥)`, with `openU`, `openP` for u_i, p_i; reason: finitely many alternatives and at least one attains U, so the suprema are these maxima
--   - reading: a deterministic, dynamically consistent maximizer exists → ∃ π deterministic with `IsDynConsistent w T π` (after every history its decision attains the lexicographic maximum (17) at the current state, and stopping submits the incumbent) that is agent-optimal and attains V_P(w | A); reason: dynamic consistency means optimality of the decision after every history; a maximizer means it attains both optima
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.1, p. 22 (PDF 23)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search
import Definitions.Def_OneTrap_Core_Index

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.1 (p. 22). For `w ∈ W_eff` and a finite technology: the Bellman values `U(R, x, h)`
and `P(R, x, h)` (optimal agent value, then best principal value among agent-optimal
continuations) are finite, measurable in `(x, h)`, satisfy the principal-favored recursion
(17), `P(A, 0, 0) = V_P(w | A)`, and a deterministic, dynamically consistent maximizer
exists. -/
theorem lemma_B_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ → ℝ) (hw : IsEffContract w)
    (T : ι → Box) :
    (∀ (R : Finset ι) (x h : ℝ),
      Ubell w T R x h ≠ ⊥ ∧ Ubell w T R x h ≠ ⊤ ∧ Pbell w T R x h ≠ ⊥ ∧ Pbell w T R x h ≠ ⊤) ∧
    (∀ R : Finset ι,
      Measurable (fun p : ℝ × ℝ => Ubell w T R p.1 p.2) ∧
      Measurable (fun p : ℝ × ℝ => Pbell w T R p.1 p.2)) ∧
    (∀ (R : Finset ι) (x h : ℝ),
      Ubell w T R x h = max ((x : ℝ) : EReal) (R.sup fun i => openU w T R x h i) ∧
      Pbell w T R x h =
        max (if ((x : ℝ) : EReal) = Ubell w T R x h then ((h : ℝ) : EReal) else ⊥)
          (R.sup fun i => if openU w T R x h i = Ubell w T R x h then openP w T R x h i else ⊥)) ∧
    Pbell w T Finset.univ 0 0 = VP w T ∧
    ∃ π : Policy Unit (Finset.univ : Finset ι),
      π.IsDeterministic ∧ IsDynConsistent w T π ∧
      π ∈ agentOptimal w T Finset.univ (nullPair w) ∧
      principalValue w T (nullPair w) π = VP w T := by sorry

end OneTrap.Core
