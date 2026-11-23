-- Prove2me | Theorems.Thm_GlobalTheory_TorusToProper_pt_nat
-- name    : GlobalTheory.TorusToProper.pt_nat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:53.486799+00:00
-- url     : https://prove2.me/theorems/30668de5-dfd3-43bb-ae90-c235cd3c10e7
-- title:
--   Torus To Proper: pt nat
-- statement:
--   The Torus To Proper construction uses the pt nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L198-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L198-L207

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
variable (K) (X : Type) [AddCommGroup X]

theorem GlobalTheory.TorusToProper.pt_nat {R R' : Type} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R'] (g : R →ₐ[K] R')
    (φ : Multiplicative X →* Rˣ) :
    pt K X R' ((Units.map (g : R →* R')).comp φ) = spm g ≫ pt K X R φ := by sorry
