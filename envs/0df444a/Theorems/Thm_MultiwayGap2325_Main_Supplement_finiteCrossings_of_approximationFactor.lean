-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_finiteCrossings_of_approximationFactor
-- name    : MultiwayGap2325.Main.Supplement.finiteCrossings_of_approximationFactor
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:40:14.380305+00:00
-- url     : https://prove2.me/theorems/1474591e-6404-4f75-b18a-36ed957291b7
-- title:
--   Lemma 5.6 — Almost-sure finite directional crossings
-- statement:
--   Fix $q\ge2$, $1/2<T<1$, a probability space $(\Xi,\mathsf P)$, and a random non-opposite cut of approximation factor $\alpha$. For almost every $\xi$, and for every face $S$, the realized cut admits a genuine finite crossing measure in every direction $(i,j)$ on the truncated face $\Omega_S$. Equivalently, there is no infinite sequence of end-separated essential crossings on any such coordinate line.
-- source:
--   STOC 2027 submission #697, Lemma 5.6, first conclusion, proof on pp.17–18 ("The approximation factor rules out infinite end-separated crossings.").

import Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps

open MeasureTheory Filter Set
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal
universe u

/-- Lemma 5.6, first conclusion: the approximation factor rules out infinite
end-separated directional crossings almost surely. -/
theorem MultiwayGap2325.Main.Supplement.finiteCrossings_of_approximationFactor
    (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1)
    (Ξ : Type u) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (α : ℝ) (hα : HasApproximationFactor C α) :
    ∀ᵐ ξ ∂P, ∀ S : Face q,
      HasFiniteCrossings T S (fun x => C.labeling (ξ, x)) := by sorry
