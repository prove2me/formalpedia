-- Prove2me | Theorems.Thm_GlobalTheory_KS_DerMorK_psi_nat
-- name    : GlobalTheory.KS.DerMorK.psi_nat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:44:19.712301+00:00
-- url     : https://prove2.me/theorems/efca9237-c37c-48de-886a-4f6fb6d5ec5b
-- title:
--   Der Mor K: psi nat
-- statement:
--   The Der Mor K construction uses the psi nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHomOfDerivation.lean#L139-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHomOfDerivation.lean#L139-L147

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

theorem GlobalTheory.KS.DerMorK.psi_nat (hd : LocDerK q p m D ⊤ d) (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi π ρ hd W' (resG X h f) = resG Y' ((ρ ≫ m).preimage_mono h) (psi π ρ hd W f) := by sorry
