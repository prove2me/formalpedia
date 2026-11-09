-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_lemma_B_3
-- name    : HitRunGaps.Spectral.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:14.381737+00:00
-- url     : https://prove2.me/theorems/c6f08b26-5815-4a5c-9ea6-16636fe9e89c
-- title:
--   Lemma B.3 — Divergence and antisymmetric energy identity
-- statement:
--   For $u\in H^1_0(\Omega;\mathbb R^n)$ on a bounded open domain, set $G_{ij}=\partial_j u_i-\partial_i u_j$. Then
--
--   $$\|\nabla u\|_2^2=\|\operatorname{div}u\|_2^2+\|G\|^2,\qquad
--   \|G\|^2=\int_\Omega\sum_{i<j}G_{ij}^2\,dx.$$
--
--   The first term uses every gradient entry; the antisymmetric energy uses only the strict upper triangle. This normalization is shared by Lemmas B.4 and B.5.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.14, Lemma B.3

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem lemma_B_3 {n : ℕ} {Ω : Set (Space n)} (hΩ : IsDomain Ω) (u : V Ω) :
    fieldEnergy u = ‖divergence u‖ ^ 2 + antiEnergy (antiGradient u) := by sorry

end HitRunGaps.Spectral
