-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_lemma_1_3
-- name    : HitRunGaps.Spectral.lemma_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:09.626551+00:00
-- url     : https://prove2.me/theorems/5dcd5be6-c043-43c2-9682-1e57ca6e29d5
-- title:
--   Lemma 1.3 — Attainment of the divergence right inverse
-- statement:
--   For a bounded nonempty open connected domain $\Omega$, suppose $C_{BA}<\infty$. Then every centered $f\in L^2(\Omega)$ admits $u\in H^1_0(\Omega;\mathbb R^n)$ such that
--
--   $$\operatorname{div}u=f,\qquad \|\nabla u\|_2^2\le C_{BA}\|f\|_2^2.$$
--
--   This asserts attainment at the optimal constant, including $f=0$, and supplies the certificates needed for both sampling bounds.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
--   - generalization: the source applies the attainment lemma to its convex sampling set → any bounded nonempty open connected domain; reason: The zero-trace Poincaré inequality and closed affine-fiber Hilbert projection proof work on every bounded domain; convex source bodies specialize directly
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.6, Lemma 1.3

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem lemma_1_3 {n : ℕ} {Ω : Set (Space n)} (hΩ : IsDomain Ω)
    (hBA : babuskaAziz Ω < ⊤) (f : Q Ω) :
    ∃ u : V Ω, divergence u = f.val ∧
      ENNReal.ofReal (fieldEnergy u) ≤ babuskaAziz Ω * ENNReal.ofReal (‖f.val‖ ^ 2) := by sorry

end HitRunGaps.Spectral
