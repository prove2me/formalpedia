-- Prove2me | Theorems.Thm_GlobalTheory_KS_DerMorK_psi_apply
-- name    : GlobalTheory.KS.DerMorK.psi_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:05.703682+00:00
-- url     : https://prove2.me/theorems/681000e4-bb4d-42bc-ad11-0e747fecc577
-- title:
--   Der Mor K: psi apply
-- statement:
--   The Der Mor K construction uses the psi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHomOfDerivation.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHomOfDerivation.lean#L135-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomOfDerivation
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMorK
variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y)
  {R : Type} [CommRing R] {D : R → K} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}

theorem GlobalTheory.KS.DerMorK.psi_apply (hd : LocDerK q p m D ⊤ d) (W : X.Opens) (f : Γ(X, W)) :
    (psi π ρ hd W f : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
    constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f) := by sorry
