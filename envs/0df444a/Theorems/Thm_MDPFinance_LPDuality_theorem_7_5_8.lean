-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_theorem_7_5_8
-- name    : MDPFinance.LPDuality.theorem_7_5_8
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:56:25.959904+00:00
-- url     : https://prove2.me/theorems/0d47f0e4-9acc-4a77-9021-da33df54eda9
-- title:
--   Theorem 7.5.8 (Strong Duality) — solving the MDP by linear programming over measures
-- statement:
--   This is the section's — and this mission's — capstone: under chunk `07a`'s contracting Structure
--   Theorem's own hypotheses, the primal program $(P)$ is solved exactly by the optimal value
--   function $J_\infty$ itself, the dual program $(D)$ is solved by the occupation measure of *any*
--   optimal stationary policy, and the two optimal values coincide with $\int J_\infty\,dp$. Finding
--   an optimal stationary policy for a contracting Markov Decision Process is, after this theorem,
--   *exactly* the same problem as solving a linear program over measures on $D$ — genuinely new
--   content relative to both Mathlib and the platform's existing finite-dimensional-vector LP duality
--   (`SmaleNinth.lp_strong_duality`, `LinearOptimization.lp_general_weak_duality`, etc.), none of
--   which operates over an infinite-dimensional space of measures.
--
--   **Moderation note.** "$IM$ a closed subspace of $\mathbb B_b$" is `IsClosedSubspaceOf` (linear, closed, containing $0$), which also supplies Theorem 7.3.5's condition (i).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 218, Theorem 7.5.8

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_LP

open MeasureTheory ProbabilityTheory

namespace MDPFinance.LPDuality

/-- **Theorem 7.5.8 (Strong duality)** (Bäuerle–Rieder, p. 218, PDF 229, the goal theorem of this
mission). Suppose the assumptions of Theorem 7.3.5 (chunk `07a`'s goal, restated here as
hypotheses) are satisfied for the closed subspace `IM \subset IB_b`. Then the following
statements hold: a) `(P)` has an optimal solution `v^* \in IM`, `v^* = J_\infty` and `val(P) =
\int J_\infty(x)\,p(dx) = val(D)`. b) `(D)` has an optimal solution `\mu^* \in M_b` and there
exists an `f^* \in F` such that `val(D) = \int r\,d\mu^* = \int J_{f^*}(x)\,p(dx)`. In particular,
the stationary policy `(f^*,f^*,\dots)` is `p`-optimal. `IM` is a closed linear subspace of
`IB_b` (which gives `0 ∈ IM` and closedness, Theorem 7.3.5's (i)). -/
theorem theorem_7_5_8 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (hαb : M.β * αb < 1) (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (hbIM : b ∈ IMs)
    (hTmaps : ∀ v ∈ IMs, (fun x => T' M v x) ∈ IMs) (Δ : Set (E → A))
    (hmax : ∀ v ∈ IMs, ∃ f ∈ Δ, IsMaximizerOf M (fun x => (v x : EReal)) f)
    (p : Measure E) (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤) :
    (∃ vstar ∈ IMs, (∀ x, Jinf M x = (vstar x : EReal)) ∧ vstar ∈ ZP M IMs ∧
        ((∫ x, vstar x ∂p : ℝ) : EReal) = valP M IMs p ∧
        valP M IMs p = valD M b IMs p) ∧
      (∃ μstar ∈ ZD M b IMs p, ∃ fstar : E → A, IsMaximizerOf M (Jinf M) fstar ∧
        valD M b IMs p = ((∫ xa, M.r xa ∂μstar : ℝ) : EReal) ∧
        valD M b IMs p = erealIntegral p (fun x => Jinfpi M M.r (fun _ => fstar) x) ∧
        IsPOptimal M p (fun _ => fstar)) := by sorry

end MDPFinance.LPDuality
