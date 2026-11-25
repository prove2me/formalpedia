-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_secOn_finitePresentation_projective
-- name    : GlobalTheory.AbLaw.secOn_finitePresentation_projective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:29:24.941717+00:00
-- url     : https://prove2.me/theorems/08187179-6fd8-477a-920a-45f551ca924f
-- title:
--   Ab Law: sec On finite Presentation projective
-- statement:
--   The Ab Law construction uses the sec On finite Presentation projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SecOnFinitePresentationProjective.lean#L44-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SecOnFinitePresentationProjective.lean#L44-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnFinitePresentationProjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw
variable {Y : Scheme.{0}} {M : LB Y} {V : Y.Opens}

theorem GlobalTheory.AbLaw.secOn_finitePresentation_projective :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V : Y.Opens), M.IsLB → IsAffineOpen V → Module.FinitePresentation Γ(Y, V) (SecOn M V) ∧ Module.Projective Γ(Y, V) (SecOn M V) := by sorry
