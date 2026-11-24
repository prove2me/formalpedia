-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_integral_cons_kernel
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.integral_cons_kernel
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:43.002464+00:00
-- url     : https://prove2.me/theorems/c807ecd3-a3d0-4b61-b3f2-bea7d3082de8
-- title:
--   Is Exp Lie Algebra: integral cons kernel
-- statement:
--   The Is Exp Lie Algebra construction uses the integral cons kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L90-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L90-L107

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.integral_cons_kernel {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    ∫ t, a (t 0) * K (Fin.tail t) * F (h.revProdExp X t * x) =
      ∫ s, ∫ t', a s * (K t' * F (h.revProdExp (Fin.tail X) t' * (h.expG (s • X 0) * x))) := by sorry
