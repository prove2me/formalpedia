-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_theorem_7_5_6
-- name    : MDPFinance.LPDuality.theorem_7_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:56:00.352566+00:00
-- url     : https://prove2.me/theorems/f71adf1d-27c5-4a5b-94c0-d67a429ce0ad
-- title:
--   Theorem 7.5.6 (Weak Duality) — the primal and dual programs are feasible and sandwich
-- statement:
--   Both the primal program $(P)$ and its dual $(D)$ have feasible points — a weighted multiple of
--   the bounding function $b$ solves $(P)$'s constraints, and any policy's occupation measure solves
--   $(D)$'s — and, as in classical finite-dimensional linear programming, every dual feasible value
--   is bounded above by every primal feasible value, with both optimal values finite. This is the
--   first genuine bridge between the Markov Decision Problem and a pair of infinite-dimensional
--   linear programs.
--
--   **Moderation note.** §7.5.2's standing setting is stated: $IM$ a closed linear subspace of $\mathbb B_b$ (`IsClosedSubspaceOf`) with $b\in IM$, besides the contracting model with $b\ge 1$ and $\int b\,dp<\infty$; the draft's weak duality had $IM$ an arbitrary set of functions.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 216, Theorem 7.5.6

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_LP

open MeasureTheory ProbabilityTheory

namespace MDPFinance.LPDuality

/-- Theorem 7.5.6 (Weak Duality) (Bäuerle–Rieder, p. 216, PDF 227). The feasible sets `Z_P` and
`Z_D` are nonempty and it holds: `-\infty < val(D) \le val(P) < \infty`. Setting of §7.5.2: a
contracting model with a bounding function `b ≥ 1`, `∫ b dp < ∞`, and `IM` a closed linear
subspace of `IB_b` with `b ∈ IM`. -/
theorem theorem_7_5_6 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (hαb : M.β * αb < 1) (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (hbIM : b ∈ IMs)
    (p : Measure E) (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤) :
    (ZP M IMs).Nonempty ∧ (ZD M b IMs p).Nonempty ∧
      (⊥ : EReal) < valD M b IMs p ∧ valD M b IMs p ≤ valP M IMs p ∧
      valP M IMs p < (⊤ : EReal) := by sorry

end MDPFinance.LPDuality
