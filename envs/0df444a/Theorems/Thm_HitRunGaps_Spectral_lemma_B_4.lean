-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_lemma_B_4
-- name    : HitRunGaps.Spectral.lemma_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:23.088584+00:00
-- url     : https://prove2.me/theorems/6da1b4e4-ae0b-4c14-b69d-236a5935cf7c
-- title:
--   Lemma B.4 — Three identities for the residual
-- statement:
--   Let $f\in Q$, let $u\in V$ be its Riesz representative characterized in Lemma B.2, and form $G_{ij}=\partial_j u_i-\partial_i u_j$. For $h=f-\operatorname{div}u$,
--
--   $$\int_\Omega h\,dx=0,\qquad \partial_i h=\sum_j\partial_jG_{ij}\quad\text{for every }i,\qquad
--   \langle h,\operatorname{div}u\rangle_Q=\|G\|^2.$$
--
--   All derivatives in the middle identity are distributional. All three conclusions describe the residual of this specified representative, rather than an arbitrary unrelated vector field.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
--   - encoding: u is the vector field given by Lemma B.2 → u satisfies the defining Riesz pairing Represents f u; reason: Lemma B.2 gives exactly one such Sobolev class; the premise identifies that same constructed object without assuming any residual conclusion
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.15, Lemma B.4

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem lemma_B_4 {n : ℕ} {Ω : Set (Space n)} (hΩ : IsDomain Ω)
    (f : Q Ω) (u : V Ω) (hu : Represents f.val u) :
    centered (f.val - divergence u) ∧
    GradEqDiv (f.val - divergence u) (antiGradient u) ∧
    inner ℝ (f.val - divergence u) (divergence u) = antiEnergy (antiGradient u) := by sorry

end HitRunGaps.Spectral
