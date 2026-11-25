-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_sum_integral_cons_kernel
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.sum_integral_cons_kernel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:50.020786+00:00
-- url     : https://prove2.me/theorems/4386008e-3548-4463-85eb-813d7f6a1dd9
-- title:
--   Is Exp Lie Algebra: sum integral cons kernel
-- statement:
--   The Is Exp Lie Algebra construction uses the sum integral cons kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L131-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L131-L145

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.sum_integral_cons_kernel {d m : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε)
    {a : ℝ → ℂ} (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε)
    {K : Fin m → (Fin d → ℝ) → ℂ} (hK : ∀ i, Continuous (K i))
    (hKs : ∀ i, tsupport (K i) ⊆ Metric.closedBall 0 ε) {F : Fin m → G → ℂ}
    (hF : ∀ i, Continuous (F i)) {f₁ : G → ℂ}
    (hd : ∀ y, f₁ y = ∑ i, ∫ t', K i t' * F i (h.revProdExp (Fin.tail X) t' * y)) (x : G) :
    ∑ i, ∫ t, a (t 0) * K i (Fin.tail t) * F i (h.revProdExp X t * x) =
      ∫ s, a s * f₁ (h.expG (s • X 0) * x) := by sorry
