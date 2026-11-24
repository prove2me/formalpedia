-- Prove2me | Theorems.Thm_GlobalTheory_LieEtale_lieMult_iff
-- name    : GlobalTheory.LieEtale.lieMult_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:08.806859+00:00
-- url     : https://prove2.me/theorems/a0f86a45-3aaa-4622-bdd3-1398b66d37fa
-- title:
--   Lie Etale: lie Mult iff
-- statement:
--   The Lie Etale construction uses the lie Mult iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L149-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L149-L159

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
variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)
variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)

theorem GlobalTheory.LieEtale.lieMult_iff (n : ℕ) : LieMult act x τ n ↔
    ∃ v : Fin n → (epsPt x ⟶ G), (∀ i, Eig (epsPtZero x) (epsPtScale x) act.act τ (v i)) ∧
      ∀ w, Eig (epsPtZero x) (epsPtScale x) act.act τ w →
        ∃! c : Fin n → k, w = (List.ofFn fun i => epsPtScale x (c i) ≫ v i).prod := by sorry
