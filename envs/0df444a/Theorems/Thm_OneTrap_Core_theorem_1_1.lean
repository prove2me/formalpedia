-- Prove2me | Theorems.Thm_OneTrap_Core_theorem_1_1
-- name    : OneTrap.Core.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:45:50.302764+00:00
-- url     : https://prove2.me/theorems/9a967b6a-26cf-4ccd-86c1-4a993b48aab2
-- title:
--   Theorem 1.1 — the one-trap property: $G_K(w)=\min\{V_P(w\mid K),\ \inf_{y\ge0,\,0\le t\le w(y)}V_P(w\mid K\cup\{\mathrm{trap}(y,t)\})\}$
-- statement:
--   For every finite known technology $K$ (independent boxes with arbitrary integrable output laws on $[0,\infty)$ and costs $\ge 0$; $K=\emptyset$ allowed) and every contract $w\in W_{\mathrm{eff}}$,
--   $$G_K(w)=\min\Big\{V_P(w\mid K),\ \inf_{\substack{y\ge 0\\ 0\le t\le w(y)}}V_P\big(w\mid K\cup\{\mathrm{trap}(y,t)\}\big)\Big\},$$
--   as extended reals, where $G_K(w)=\inf_{A\in E_f(K)}V_P(w\mid A)$ ranges over all finite independent extensions of $K$ and $\mathrm{trap}(y,t)$ returns $y$ with probability one at cost $w(y)-t$. Both sides may be $-\infty$.
--
--   Differences from the source:
--   - encoding: box i: output law F_i on [0, ∞), integrable (Assumption 2.1), deterministic cost c_i ≥ 0 → `Box`: a `ProbabilityMeasure ℝ` with nonnegative outputs almost surely and integrable identity, and a real cost ≥ 0; a technology is `T : ι → Box` with `[Fintype ι]`, joint law the product measure; reason: the same objects; independence is the product law
--   - encoding: a contract is a Borel function w : R+ → R+; W_eff adds w(0) = 0 and w(y) ≤ L(1 + y) for one L < ∞ → `w : ℝ → ℝ` Borel on ℝ with `0 ≤ w y` for `y ≥ 0` (`IsContract`), plus `w 0 = 0` and `∃ L, ∀ y ≥ 0, w y ≤ L * (1 + y)` (`IsEffContract`); reason: outputs are almost surely nonnegative, so values of w on (−∞, 0) never matter, and every Borel function on R+ extends to a Borel function on ℝ
--   - encoding: a policy assigns to every history (distinct actions with observed outputs) a probability distribution over taking an unopened action or stopping and submitting the null output or an observed output, Borel in the observed outputs → `Policy`: a rule of the opened set S, the outputs y (pre-sampled from the product law) and one seed u uniform on [0, 1] that reads y only on S, is measurable, opens only unopened boxes and submits only available outcomes; reason: the order in which S was opened is itself a function of the rule, y on S and u, and one uniform seed generates independent randomizations for every step (and conversely), so the laws of (opened set, submitted output) are the same
--   - encoding: expected payoffs U_A, P_A in the extended reals (Appendix A) → `eexp`: lower Lebesgue integral of the positive part minus that of the negative part, in EReal; reason: the convention of Appendix A; never the Bochner integral; ⊤ − ⊤ (= ⊥ in EReal) does not arise for these payoffs because the agent payoff is bounded below and the principal payoff above by integrable variables
--   - encoding: V_P(w | A) = max of P_A(w, π) over Σ⋆(w, A) = argmax U_A(w, ·) (Definition 2.2) → `VP w T` = `sSup` in EReal of `principalValue` over `agentOptimal` (⊥ if that set were empty); the null output is the initial outcome with pair (w 0, 0 − w 0); reason: both maxima are attained (Fact A.1), and an attained supremum is the maximum
--   - encoding: G_K(w) = inf over A ∈ E_f(K) of V_P(w | A) → `robustGuarantee w K = ⨅ (n : ℕ) (N : Fin n → Box), VP w (Sum.elim K N)` in EReal; reason: every finite extension is K plus n fresh boxes for some n, up to relabelling; n = 0 is A = K
--   - encoding: K ∪ {trap(y, t)}, trap(y, t) a fresh box returning y with probability one at cost w(y) − t (Definition 3.1) → `withTrap w K y t hy ht` = `Sum.elim K (fun _ : Unit => trap w y t hy ht)` on `κ ⊕ Unit`, the trap having law δ_y and cost w y − t; reason: one fresh box; the side conditions y ≥ 0 and t ≤ w(y) are carried by the proofs hy, ht
--   - encoding: inf over y ≥ 0 and 0 ≤ t ≤ w(y) → `⨅ (y) (hy : 0 ≤ y) (t) (_ : 0 ≤ t) (ht : t ≤ w y)` in EReal; reason: the same index set
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Theorem 1.1, p. 1 (PDF 2); proof p. 9 (PDF 10)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search

open MeasureTheory

namespace OneTrap.Core

/-- Theorem 1.1 (p. 1), the one-trap property. For every finite known technology `K` and every
contract `w ∈ W_eff`,
`G_K(w) = min {V_P(w | K), inf_{y ≥ 0, 0 ≤ t ≤ w(y)} V_P(w | K ∪ {trap(y, t)})}`
in the extended reals. -/
theorem theorem_1_1 {κ : Type*} [Fintype κ] [DecidableEq κ] (w : ℝ → ℝ) (hw : IsEffContract w)
    (K : κ → Box) :
    robustGuarantee w K =
      min (VP w K)
        (⨅ (y : ℝ) (hy : 0 ≤ y) (t : ℝ) (_ : 0 ≤ t) (ht : t ≤ w y),
          VP w (withTrap w K y t hy ht)) := by sorry

end OneTrap.Core
