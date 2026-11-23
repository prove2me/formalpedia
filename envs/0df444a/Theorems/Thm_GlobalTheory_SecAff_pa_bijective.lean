-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_pa_bijective
-- name    : GlobalTheory.SecAff.pa_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:45:39.719328+00:00
-- url     : https://prove2.me/theorems/d965a19b-363c-4c00-94c7-656a50c87e90
-- title:
--   Sec Aff: pa bijective
-- statement:
--   The Sec Aff construction uses the pa bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L63-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}

theorem GlobalTheory.SecAff.pa_bijective (φ : X' ⟶ X) [IsOpenImmersion φ] {U : X.Opens} {V : X'.Opens}
    (h : V ≤ φ ⁻¹ᵁ U) (h' : φ ⁻¹ᵁ U ≤ V) (hU : U ≤ φ.opensRange) :
    Function.Bijective (pa φ h) := by sorry
