-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_exists_sum
-- name    : GlobalTheory.WeierstrassCurve.exists_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:49:22.316852+00:00
-- url     : https://prove2.me/theorems/3496f748-12a0-48c6-bfc1-b1219accad51
-- title:
--   Weierstrass Curve: exists sum
-- statement:
--   The Weierstrass Curve construction uses the exists sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L352-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L352-L375

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [W.IsElliptic]

theorem GlobalTheory.WeierstrassCurve.exists_sum {T : Over (Spec (.of R))} [IsReduced T.left] (p q : T ⟶ schemeOver W) :
    ∃ s : T ⟶ schemeOver W, ∀ (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ T),
      x ≫ s = fieldAdd W k (x ≫ p) (x ≫ q) := by sorry
