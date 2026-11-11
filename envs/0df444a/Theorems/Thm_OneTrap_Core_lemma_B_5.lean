-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_5
-- name    : OneTrap.Core.lemma_B_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:47:03.630981+00:00
-- url     : https://prove2.me/theorems/20ba40eb-1c68-4ad4-8785-1815e5c1cf49
-- title:
--   Lemma B.5 — the infinite-index block is opened by every agent-optimal policy, first by some PF-optimal one, and leaves the state $(A\setminus I_\infty,M_\infty,H_\infty)$
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$ and a finite technology $A$; let $I_\infty=\{i\in A:\rho_i=+\infty\}$. Every agent-optimal policy opens all boxes of $I_\infty$ almost surely, and some principal-favored optimal policy opens them before any finite-index box. Starting from a state $(A,x,h)$ with finite $x,h$, the state after opening the block is $(A\setminus I_\infty,M_\infty,H_\infty)$ with
--   $$(M_\infty,H_\infty)=\max\nolimits_{\mathrm{lex}}\big(\{(x,h)\}\cup\{(X_i,H_i):i\in I_\infty\}\big),$$
--   so that $U(A,x,h)=-\sum_{i\in I_\infty}c_i+\mathbb E[U(A\setminus I_\infty,M_\infty,H_\infty)]$ (the costs are zero) and $P(A,x,h)=\mathbb E[P(A\setminus I_\infty,M_\infty,H_\infty)]$.
--
--   Differences from the source:
--   - encoding: a policy assigns to every history (distinct actions with observed outputs) a probability distribution over taking an unopened action or stopping and submitting the null output or an observed output, Borel in the observed outputs → `Policy`: a rule of the opened set S, the outputs y (pre-sampled from the product law) and one seed u uniform on [0, 1] that reads y only on S, is measurable, opens only unopened boxes and submits only available outcomes; reason: the order in which S was opened is itself a function of the rule, y on S and u, and one uniform seed generates independent randomizations for every step (and conversely), so the laws of (opened set, submitted output) are the same
--   - encoding: expected payoffs U_A, P_A in the extended reals (Appendix A) → `eexp`: lower Lebesgue integral of the positive part minus that of the negative part, in EReal; reason: the convention of Appendix A; never the Bochner integral; ⊤ − ⊤ (= ⊥ in EReal) does not arise for these payoffs because the agent payoff is bounded below and the principal payoff above by integrable variables
--   - encoding: V_P(w | A) = max of P_A(w, π) over Σ⋆(w, A) = argmax U_A(w, ·) (Definition 2.2) → `VP w T` = `sSup` in EReal of `principalValue` over `agentOptimal` (⊥ if that set were empty); the null output is the initial outcome with pair (w 0, 0 − w 0); reason: both maxima are attained (Fact A.1), and an attained supremum is the maximum
--   - encoding: U(R, x, h) and P(R, x, h): the agent's optimal value from the state and the best principal value among the policies attaining it → `Ubell`/`Pbell`: the optimal values of the search problem whose openable boxes are R and whose only initially available outcome is (x, h) (agent value as a supremum over policies, principal value as `pfValue`); reason: stopping yields exactly (x, h), as u_stop = x and p_stop = h in (17); earlier outcomes are lexicographically below the incumbent and the remaining outputs are independent of the past
--   - reading: some PF-optimal policy opens them before any finite-index box → ∃ π ∈ Σ⋆ attaining V_P(w | A) such that at every opened set at which some infinite-index box is unopened, any box it opens has infinite index; reason: the meaning of "before any finite-index box"
--   - reading: starting from (A, x, h), the state after opening the infinite-index block is (A \ I∞, M∞, H∞) → U(A, x, h) = −Σ_{I∞} c_i + E[U(A \ I∞, M∞, H∞)] and P(A, x, h) = E[P(A \ I∞, M∞, H∞)], with (M∞, H∞) = `stateAfter w (x, h) I∞ y`; reason: the claim about the continuation that the proof of Lemma B.9 uses; the costs of I∞ are zero by Lemma B.12, so the cost term vanishes
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.5, p. 24 (PDF 25)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search
import Definitions.Def_OneTrap_Core_Index

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.5 (p. 24). Let `I∞ = {i : ρ_i = +∞}`. Every agent-optimal policy opens all boxes of
`I∞` almost surely; some principal-favored optimal policy opens them before any finite-index
box; and from a state `(A, x, h)` with finite `x, h` the state after opening the block is
`(A \ I∞, M∞, H∞)` with `(M∞, H∞) = maxlex ({(x, h)} ∪ {(X_i, H_i) : i ∈ I∞})`, so that
`U(A, x, h)` and `P(A, x, h)` are the expectations of `U` and `P` at that state (minus the
block's costs, which are zero). -/
theorem lemma_B_5 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ → ℝ) (hw : IsEffContract w)
    (T : ι → Box) :
    (∀ π ∈ agentOptimal w T Finset.univ (nullPair w),
      ∀ i, resv w (T i) = ⊤ → ∀ᵐ ω ∂(jointLaw T), i ∈ (π.run ω.1 ω.2).1) ∧
    (∃ π ∈ agentOptimal w T Finset.univ (nullPair w),
      principalValue w T (nullPair w) π = VP w T ∧
      ∀ (S : Finset ι) (y : ι → ℝ) (u : ℝ) (i : ι),
        (∃ j, resv w (T j) = ⊤ ∧ j ∉ S) → (π.rule S y u).box? = some i → resv w (T i) = ⊤) ∧
    (∀ x h : ℝ,
      Ubell w T Finset.univ x h =
        -(((∑ i ∈ Finset.univ.filter (fun i => resv w (T i) = ⊤), (T i).cost : ℝ)) : EReal) +
          eexp (outputLaw T) (fun y =>
            Ubell w T (Finset.univ \ Finset.univ.filter (fun i => resv w (T i) = ⊤))
              (stateAfter w (x, h) (Finset.univ.filter (fun i => resv w (T i) = ⊤)) y).1
              (stateAfter w (x, h) (Finset.univ.filter (fun i => resv w (T i) = ⊤)) y).2) ∧
      Pbell w T Finset.univ x h =
          eexp (outputLaw T) (fun y =>
            Pbell w T (Finset.univ \ Finset.univ.filter (fun i => resv w (T i) = ⊤))
              (stateAfter w (x, h) (Finset.univ.filter (fun i => resv w (T i) = ⊤)) y).1
              (stateAfter w (x, h) (Finset.univ.filter (fun i => resv w (T i) = ⊤)) y).2)) := by sorry

end OneTrap.Core
