-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_proposition_2_1
-- name    : HitRunGaps.Spectral.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:09.909345+00:00
-- url     : https://prove2.me/theorems/530f9cee-4957-4769-88d6-be3502a1a08c
-- title:
--   Proposition 2.1 — Hit-and-Run gap via Babuška–Aziz
-- statement:
--   For every dimension $n\ge1$ and nonempty bounded open convex $K$, if $C_{BA}<\infty$, then
--
--   $$\lambda_{HR}\ge\frac{n+2}{n(2+C_{BA})}\gtrsim\frac1{1+C_{BA}}.$$
--
--   The comparison constant is positive and universal, chosen before the dimension and body. Both the exact fraction and the adjacent universal comparison are retained. This is the continuous Hit-and-Run estimate used in the main theorem.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
--   - encoding: the operator Dirichlet form of the actual reversible chord sampler → the one-half squared-jump integral against the published chord laws; reason: Reversibility identifies this nonnegative form with the source inner product, so the Rayleigh infimum covers the same L² classes
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.7, Proposition 2.1

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem proposition_2_1 : ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n →
    ∀ K : Set (Space n), IsOpen K → Bornology.IsBounded K → Convex ℝ K → K.Nonempty →
    babuskaAziz K < ⊤ →
      (n + 2 : ENNReal) / ((n : ENNReal) * (2 + babuskaAziz K)) ≤ hitRunGap K ∧
      ENNReal.ofReal c / (1 + babuskaAziz K) ≤
        (n + 2 : ENNReal) / ((n : ENNReal) * (2 + babuskaAziz K)) := by sorry

end HitRunGaps.Spectral
