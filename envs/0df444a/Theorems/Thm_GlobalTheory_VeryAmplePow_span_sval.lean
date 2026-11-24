-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_span_sval
-- name    : GlobalTheory.VeryAmplePow.span_sval
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:42.600804+00:00
-- url     : https://prove2.me/theorems/cacd22fa-dbd0-409b-a99e-ad898d9c6ace
-- title:
--   Very Ample Pow: span sval
-- statement:
--   The Very Ample Pow construction uses the span sval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L274-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L274-L289

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

theorem GlobalTheory.VeryAmplePow.span_sval {a : ℤ} {T : Over S} {I : Type} [Fintype I] (b : I → LB.Sec (LPow A L a T))
    (hb : Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L a T)) = ⊤)
    (s : LB.Sec (LPow A L a T)) : ∃ c : I → Γ(T.left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J,
      Good L z J → sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J =
        ∑ i, gs (r ≫ (fst T A).left) z ⊤ (c i) *
          sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (b i) r z J := by sorry
