-- Prove2me | Theorems.Thm_GlobalTheory_RigidLinearisation_exists_normalised
-- name    : GlobalTheory.RigidLinearisation.exists_normalised
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:09.46753+00:00
-- url     : https://prove2.me/theorems/c124075f-fd11-4f72-a649-f83bde8d8a80
-- title:
--   Rigid Linearisation: exists normalised
-- statement:
--   The Rigid Linearisation construction uses the exists normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearisation.lean#L76-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearisation.lean#L76-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearisation
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.RigidLinearisation

theorem GlobalTheory.RigidLinearisation.exists_normalised {X Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (p : Y ⟶ X) (e : X ⟶ Y) (he : e ≫ p = 𝟙 X)
    (ρ : X ⟶ X) (τ : Y ⟶ Y) (hτ : e ≫ τ = ρ ≫ e) (r : (L.pull e).Gen) (hr : r.IsGen) (h : LBIso L (L.pull τ)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (b : Z ⟶ X) (z : Z) (J), Good L z J →
        val u (b ≫ e) z J = val r b z J * (val r (b ≫ ρ) z J)⁻¹ := by sorry
