-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_proposition_2_2
-- name    : HitRunGaps.Spectral.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:15:48.7412+00:00
-- url     : https://prove2.me/theorems/19d0035e-6e01-40f7-ba3c-188cd319254f
-- title:
--   Proposition 2.2 — Coordinate Hit-and-Run gap via Babuška–Aziz
-- statement:
--   For every dimension $n\ge1$, nonempty bounded open convex $K$, and fixed orthonormal coordinate basis, if $C_{BA}<\infty$, then
--
--   $$\lambda_{CHAR}\ge\frac1{nC_{BA}}.$$
--
--   The chain selects each coordinate with probability $1/n$ and samples the entire corresponding chord. This is the coordinate sampler bound needed alongside Proposition 2.1.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
--   - encoding: the operator Dirichlet form of the actual reversible chord sampler → the one-half squared-jump integral against the published chord laws; reason: Reversibility identifies this nonnegative form with the source inner product, so the Rayleigh infimum covers the same L² classes
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.8, Proposition 2.2

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem proposition_2_2 {n : ℕ} (hn : 1 ≤ n) {K : Set (Space n)}
    (hopen : IsOpen K) (hbounded : Bornology.IsBounded K) (hconvex : Convex ℝ K)
    (hne : K.Nonempty) (hBA : babuskaAziz K < ⊤)
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) :
    1 / ((n : ENNReal) * babuskaAziz K) ≤ coordinateGap K b := by sorry

end HitRunGaps.Spectral
