-- Prove2me | Theorems.Thm_GlobalTheory_KS_ProdLift_main
-- name    : GlobalTheory.KS.ProdLift.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:28:11.524799+00:00
-- url     : https://prove2.me/theorems/4b7e3c1c-ebbf-4cc0-8603-4b447c5755c0
-- title:
--   Prod Lift: main
-- statement:
--   The Prod Lift construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L198-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L198-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.ProdLift

theorem GlobalTheory.KS.ProdLift.main : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (A : Over (Sp R)) (A₀ : Over (Sp K)) (m : A₀.left ⟶ A.left) (m₂ : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left) (D : R → K) (W W' : A.left.Opens), m ≫ A.hom = A₀.hom ≫ spMap x₀ → IsSquare m m₂ → IsAffineOpen W → IsAffineOpen W' → ∀ Q, Q = (fst A A).left ⁻¹ᵁ W ⊓ (snd A A).left ⁻¹ᵁ W' → (∀ d d', LocDerK A₀.hom A.hom m D W d → LocDerK A₀.hom A.hom m D W' d' → ∃ d₂, LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ ∧ (∀ f, d₂ Q (pbT (fst A A).left f Q) = pbT (fst A₀ A₀).left (d W f) _) ∧ ∀ f, d₂ Q (pbT (snd A A).left f Q) = pbT (snd A₀ A₀).left (d' W' f) _) ∧ ∀ d₂ d₂', LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ → LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂' → (∀ f : Γ(A.left, W), d₂ Q (pbT (fst A A).left f Q) = d₂' Q (pbT (fst A A).left f Q)) → (∀ f : Γ(A.left, W'), d₂ Q (pbT (snd A A).left f Q) = d₂' Q (pbT (snd A A).left f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by sorry
