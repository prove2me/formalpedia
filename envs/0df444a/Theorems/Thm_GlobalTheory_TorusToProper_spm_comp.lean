-- Prove2me | Theorems.Thm_GlobalTheory_TorusToProper_spm_comp
-- name    : GlobalTheory.TorusToProper.spm_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:40.012927+00:00
-- url     : https://prove2.me/theorems/c924309a-822e-4ad8-bfec-e8769cb4d2b6
-- title:
--   Torus To Proper: spm comp
-- statement:
--   The Torus To Proper construction uses the spm comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L28-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]

theorem GlobalTheory.TorusToProper.spm_comp {R R' R'' : Type} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    [CommRing R''] [Algebra K R''] (g : R →ₐ[K] R') (h : R' →ₐ[K] R'') :
    spm h ≫ spm g = spm (h.comp g) := by sorry
