-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_lemma_B_2
-- name    : HitRunGaps.Spectral.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:49.833657+00:00
-- url     : https://prove2.me/theorems/14d6deb8-dfdc-4ebc-ac45-69db1d5b4e79
-- title:
--   Lemma B.2 — Riesz representative of the divergence functional
-- statement:
--   On any bounded open domain $\Omega$, put $Q=L^2_0(\Omega)$ and $V=H^1_0(\Omega;\mathbb R^n)$ with the gradient inner product. For every $f\in Q$ there is a unique $u\in V$ such that
--
--   $$\langle f,\operatorname{div}v\rangle_Q=\langle u,v\rangle_V\quad\text{for every }v\in V,$$
--
--   and this $u$ satisfies
--
--   $$\|\nabla u\|_2=\sup_{v\in V,\ v\ne0}\frac{\langle f,\operatorname{div}v\rangle_Q}{\|\nabla v\|_2}.$$
--
--   Uniqueness is among all fields with the pairing property (not only among those also satisfying the norm identity), and is equality of Sobolev equivalence classes. This identifies the vector field used in Lemma B.4, including the zero input.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.14, Lemma B.2

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem lemma_B_2 {n : ℕ} {Ω : Set (Space n)} (hΩ : IsDomain Ω) (f : Q Ω) :
    (∃! u : V Ω, Represents f.val u) ∧
      ∀ u : V Ω, Represents f.val u → Real.sqrt (fieldEnergy u) = dualNorm f.val := by sorry

end HitRunGaps.Spectral
