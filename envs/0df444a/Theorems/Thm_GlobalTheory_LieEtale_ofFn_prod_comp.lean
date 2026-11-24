-- Prove2me | Theorems.Thm_GlobalTheory_LieEtale_ofFn_prod_comp
-- name    : GlobalTheory.LieEtale.ofFn_prod_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:05:37.206263+00:00
-- url     : https://prove2.me/theorems/faf486fc-975a-4740-aa31-134238b2af9a
-- title:
--   Lie Etale: of Fn prod comp
-- statement:
--   The Lie Etale construction uses the of Fn prod comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L67-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LieEtale
variable {S : Scheme.{0}} {O k : Type} {P E : Over S}

theorem GlobalTheory.LieEtale.ofFn_prod_comp {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] {n : ℕ}
    (u : Fin n → (E ⟶ A)) : (List.ofFn u).prod ≫ ψ = (List.ofFn fun i => u i ≫ ψ).prod := by sorry
