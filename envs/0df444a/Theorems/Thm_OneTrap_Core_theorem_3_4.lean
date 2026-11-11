-- Prove2me | Theorems.Thm_OneTrap_Core_theorem_3_4
-- name    : OneTrap.Core.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:45:48.322192+00:00
-- url     : https://prove2.me/theorems/31f7eaf7-4926-4ae3-b4b3-188c9fd3161f
-- title:
--   Theorem 3.4 — one-trap approximation for general technologies
-- statement:
--   Let $w\in W_{\mathrm{eff}}$, $A\in E_f(K)$ and $\varepsilon>0$. There is a technology $\tilde A$, equal to $K$ or to $K\cup\{\mathrm{trap}(y,t)\}$ for some $y\ge 0$ and $0\le t\le w(y)$, such that
--   $$V_P(w\mid\tilde A)\le V_P(w\mid A)+\varepsilon .$$
--   Output laws are arbitrary integrable laws on $[0,\infty)$, costs are $\ge 0$, and reservation values may be infinite or tied.
--
--   Differences from the source:
--   - encoding: box i: output law F_i on [0, ∞), integrable (Assumption 2.1), deterministic cost c_i ≥ 0 → `Box`: a `ProbabilityMeasure ℝ` with nonnegative outputs almost surely and integrable identity, and a real cost ≥ 0; a technology is `T : ι → Box` with `[Fintype ι]`, joint law the product measure; reason: the same objects; independence is the product law
--   - encoding: a contract is a Borel function w : R+ → R+; W_eff adds w(0) = 0 and w(y) ≤ L(1 + y) for one L < ∞ → `w : ℝ → ℝ` Borel on ℝ with `0 ≤ w y` for `y ≥ 0` (`IsContract`), plus `w 0 = 0` and `∃ L, ∀ y ≥ 0, w y ≤ L * (1 + y)` (`IsEffContract`); reason: outputs are almost surely nonnegative, so values of w on (−∞, 0) never matter, and every Borel function on R+ extends to a Borel function on ℝ
--   - encoding: a policy assigns to every history (distinct actions with observed outputs) a probability distribution over taking an unopened action or stopping and submitting the null output or an observed output, Borel in the observed outputs → `Policy`: a rule of the opened set S, the outputs y (pre-sampled from the product law) and one seed u uniform on [0, 1] that reads y only on S, is measurable, opens only unopened boxes and submits only available outcomes; reason: the order in which S was opened is itself a function of the rule, y on S and u, and one uniform seed generates independent randomizations for every step (and conversely), so the laws of (opened set, submitted output) are the same
--   - encoding: expected payoffs U_A, P_A in the extended reals (Appendix A) → `eexp`: lower Lebesgue integral of the positive part minus that of the negative part, in EReal; reason: the convention of Appendix A; never the Bochner integral; ⊤ − ⊤ (= ⊥ in EReal) does not arise for these payoffs because the agent payoff is bounded below and the principal payoff above by integrable variables
--   - encoding: V_P(w | A) = max of P_A(w, π) over Σ⋆(w, A) = argmax U_A(w, ·) (Definition 2.2) → `VP w T` = `sSup` in EReal of `principalValue` over `agentOptimal` (⊥ if that set were empty); the null output is the initial outcome with pair (w 0, 0 − w 0); reason: both maxima are attained (Fact A.1), and an attained supremum is the maximum
--   - encoding: an admissible extension A ⊇ K (finite, independent, every new box with a fresh label) → `Sum.elim K N` with `N : ν → Box` for a finite type ν (for G_K: ν = Fin n); reason: relabelling only; any number of new boxes with any admissible laws and costs, duplicates of known boxes, and A = K (ν empty) are all included
--   - encoding: K ∪ {trap(y, t)}, trap(y, t) a fresh box returning y with probability one at cost w(y) − t (Definition 3.1) → `withTrap w K y t hy ht` = `Sum.elim K (fun _ : Unit => trap w y t hy ht)` on `κ ⊕ Unit`, the trap having law δ_y and cost w y − t; reason: one fresh box; the side conditions y ≥ 0 and t ≤ w(y) are carried by the proofs hy, ht
--   - encoding: V_P(w | Ã) ≤ V_P(w | A) + ε → the same inequality in EReal with ε coerced from ℝ; reason: values are extended reals; for w ∈ W_eff they are real (Proposition 2.3)
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Theorem 3.4, p. 8 (PDF 9); full proof p. 32 (PDF 33)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search

open MeasureTheory

namespace OneTrap.Core

/-- Theorem 3.4 (p. 8), one-trap approximation. Let `w ∈ W_eff`, `A = K ⊕ N ∈ E_f(K)` and
`ε > 0`. There is `Ã = K` or `Ã = K ∪ {trap(y, t)}` with `y ≥ 0` and `0 ≤ t ≤ w(y)` such that
`V_P(w | Ã) ≤ V_P(w | A) + ε`. -/
theorem theorem_3_4 {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (w : ℝ → ℝ) (hw : IsEffContract w) (K : κ → Box) (N : ν → Box) (ε : ℝ) (hε : 0 < ε) :
    VP w K ≤ VP w (Sum.elim K N) + ((ε : ℝ) : EReal) ∨
    ∃ (y t : ℝ) (hy : 0 ≤ y) (ht : t ≤ w y), 0 ≤ t ∧
      VP w (withTrap w K y t hy ht) ≤ VP w (Sum.elim K N) + ((ε : ℝ) : EReal) := by sorry

end OneTrap.Core
