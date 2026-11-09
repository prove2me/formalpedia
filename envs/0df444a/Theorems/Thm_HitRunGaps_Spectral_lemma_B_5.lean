-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_lemma_B_5
-- name    : HitRunGaps.Spectral.lemma_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:40.19469+00:00
-- url     : https://prove2.me/theorems/d63e9161-1d80-4c63-9622-4c46854326e3
-- title:
--   Lemma B.5 — Boundary-weighted estimate and improved Poincaré consequence
-- statement:
--   Let $\Omega$ be any bounded open domain, $h\in Q$, and $G$ a square-integrable antisymmetric matrix field satisfying $\nabla h=\operatorname{div}G$ distributionally. With the upper-triangular norm from Lemma B.3,
--
--   $$\|\delta\nabla h\|_2\le2\|G\|.$$
--
--   If $C_{IPI}<\infty$, also
--
--   $$\|h\|_2^2\le4C_{IPI}\|G\|^2.$$
--
--   The weighted derivative is asserted to exist and have finite energy. There is no hypothesis that $h\in H^1(\Omega)$, that the boundary is smooth, or that $\Omega$ is convex. Both estimates are retained for the residual application in Theorem 1.4.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
--   - encoding: the norm of δ∇h is meaningful in the conclusion → a locally integrable weak gradient exists and its weighted energy is finite before converting the energy to a real norm; reason: This makes the regularity implicit in the source norm explicit, without adding global H¹ membership as a premise
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.15, Lemma B.5

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem lemma_B_5 {n : ℕ} {Ω : Set (Space n)} (hΩ : IsDomain Ω)
    (h : Q Ω) (G : Fin n → Fin n → L2 Ω) (hG : ∀ i j, G i j = -G j i)
    (heq : GradEqDiv h.val G) :
    (∃ g : Fin n → Space n → ℝ,
      (∀ i, HunterPDE.Shared.HasWeakDeriv Ω (Pi.single i 1) h.val (g i)) ∧
      weightedEnergy Ω g < ⊤ ∧
      Real.sqrt (weightedEnergy Ω g).toReal ≤ 2 * Real.sqrt (antiEnergy G)) ∧
    (improvedPoincare Ω < ⊤ →
      ENNReal.ofReal (‖h.val‖ ^ 2) ≤ 4 * improvedPoincare Ω * ENNReal.ofReal (antiEnergy G)) := by sorry

end HitRunGaps.Spectral
