-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_torusExtension_of_comp_eq
-- name    : GlobalTheory.nonempty_torusExtension_of_comp_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:54:06.649835+00:00
-- url     : https://prove2.me/theorems/2717a0cd-ac5f-4982-9d33-4fd30efbfb0e
-- title:
--   Global Theory: nonempty torus Extension of comp eq
-- statement:
--   The Global Theory construction uses the nonempty torus Extension of comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteDvrTorusExtensionSpecialFibre.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteDvrTorusExtensionSpecialFibre.lean#L16-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteDvrTorusExtensionSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open IsLocalRing

theorem GlobalTheory.nonempty_torusExtension_of_comp_eq {K : Type} [Field K] {S S₁ S₂ : Scheme.{0}} {a : S₁ ⟶ S}
    {b : Spec (CommRingCat.of K) ⟶ S₁} {c : S₂ ⟶ S} {d : Spec (CommRingCat.of K) ⟶ S₂} (e : b ≫ a = d ≫ c)
    (G : Over S) [GrpObj G] (h : Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G)))) :
    Nonempty (TorusExtension ((Over.pullback d).obj ((Over.pullback c).obj G))) := by sorry
