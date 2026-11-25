-- Prove2me | Theorems.Thm_GlobalTheory_SharpFamRel_rel_of_isSharp
-- name    : GlobalTheory.SharpFamRel.rel_of_isSharp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:31.428271+00:00
-- url     : https://prove2.me/theorems/ad2e9354-37c8-49cc-939a-2968dd3fa5fb
-- title:
--   Sharp Fam Rel: rel of is Sharp
-- statement:
--   The Sharp Fam Rel construction uses the rel of is Sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L163-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L163-L223

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpFamRel
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
variable {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {S : Scheme.{0}} {s : S ⟶ Sp o}

theorem GlobalTheory.SharpFamRel.rel_of_isSharp {h : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t : TObj g k J b s}
    {c : SiegPre h k (b.ζ : o) s} (H : IsSharp W a bas t c) :
    (∀ j j' j'', a j'' = a j * a j' → t.act j'' = t.act j' ≫ t.act j) ∧
    (∀ j j' j'', a j'' = a j + a j' → t.act j'' = t.act j * t.act j') ∧ (∀ j, a j = 1 → t.act j = 𝟙 t.A) ∧
    ∀ j i, t.pt i ≫ t.act j =
      (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod := by sorry
