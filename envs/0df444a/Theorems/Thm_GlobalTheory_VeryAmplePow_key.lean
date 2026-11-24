-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_key
-- name    : GlobalTheory.VeryAmplePow.key
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:50:52.125864+00:00
-- url     : https://prove2.me/theorems/f77d752c-1d75-4f51-8747-ca4d11f5b6f2
-- title:
--   Very Ample Pow: key
-- statement:
--   The Very Ample Pow construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L291-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L291-L311

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}

theorem GlobalTheory.VeryAmplePow.key {a : ℤ} {T : Over S} {I : Type} [Fintype I] (b : I → LB.Sec (LPow A L a T)) (T' : Over S) (h : T' ⟶ T)
    (hb : ∀ b' : I → LB.Sec (LPow A L a T'), (∀ i, IsPullSec A L a (h ▷ A) (whiskerRight_snd h A) (b i) (b' i)) →
      Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L a T')) = ⊤)
    (s : LB.Sec (LPow A L a T')) : ∃ c : I → Γ(T'.left, ⊤), ∀ (x : T' ⟶ A) (g : T'.left ⟶ (T ⊗ A).left),
      g ≫ (fst T A).left = h.left → g ≫ (snd T A).left = x.left →
      ∀ (τ : LB.Gen (LB.LinComb L (Y := T'.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))) (v : Γ(T'.left, ⊤)),
      IsValueAt A L a s x τ v → ∀ z J, Good L z J → gs (𝟙 _) z ⊤ v * (val τ (𝟙 _) z J).val =
        ∑ i, gs (𝟙 _) z ⊤ (c i) * sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (b i) g z J := by sorry
