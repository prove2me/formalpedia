-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_lemma_B_1
-- name    : HitRunGaps.Spectral.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:13.547728+00:00
-- url     : https://prove2.me/theorems/6b4d9b5b-e7f3-498a-9e51-f9cd0133960b
-- title:
--   Lemma B.1 — Full equivalence between right inverse and inf-sup bound
-- statement:
--   For any bounded open domain $\Omega$ and every real $C>0$, the following conditions are equivalent:
--
--   1. Every $f\in Q$ has $v\in V$ with $\operatorname{div}v=f$ and $\|\nabla v\|_2^2\le C\|f\|_2^2$.
--   2. Every $f\in Q$ satisfies
--
--   $$\|f\|_2^2\le C\left(\sup_{v\in V,\ v\ne0}\frac{\langle f,\operatorname{div}v\rangle_Q}{\|\nabla v\|_2}\right)^2.$$
--
--   Both implications, including right-inverse existence, are targets. The supremum is that of the actual divergence functional, not an arbitrary supplied dual quantity.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.14, Lemma B.1

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem lemma_B_1 {n : ℕ} {Ω : Set (Space n)} (hΩ : IsDomain Ω)
    (C : ℝ) (hC : 0 < C) :
    (∀ f : Q Ω, ∃ v : V Ω, divergence v = f.val ∧
      fieldEnergy v ≤ C * ‖f.val‖ ^ 2) ↔
    (∀ f : Q Ω, ‖f.val‖ ^ 2 ≤ C * (dualNorm f.val) ^ 2) := by sorry

end HitRunGaps.Spectral
