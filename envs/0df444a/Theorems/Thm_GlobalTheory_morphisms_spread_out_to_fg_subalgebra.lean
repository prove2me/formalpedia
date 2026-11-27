-- Prove2me | Theorems.Thm_GlobalTheory_morphisms_spread_out_to_fg_subalgebra
-- name    : GlobalTheory.morphisms_spread_out_to_fg_subalgebra
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:28:35.384096+00:00
-- url     : https://prove2.me/theorems/aefa3545-3d3a-4c4e-b89c-1b7e900c7e8c
-- title:
--   Global Theory: morphisms spread out to fg subalgebra
-- statement:
--   The Global Theory construction uses the morphisms spread out to fg subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L323-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L323-L334

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.morphisms_spread_out_to_fg_subalgebra (k : IntermediateField ℚ ℂ) (B Z : Scheme.{0})
    (pB : B ⟶ Sp k) (pZ : Z ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB]
    [LocallyOfFinitePresentation pZ] (n : ℕ)
    (φ : Fin n → (pullback pB (spMap (algebraMap k ℂ)) ⟶ Z))
    (hφ : ∀ i, φ i ≫ pZ = pullback.fst _ _ ≫ pB) (R₀ : Subalgebra k ℂ) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k ℂ) (ψ : Fin n → (pullback pB (spMap (algebraMap k R)) ⟶ Z))
      (j : pullback pB (spMap (algebraMap k ℂ)) ⟶ pullback pB (spMap (algebraMap k R))),
      R.FG ∧ R₀ ≤ R ∧ j ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R.val.toRingHom ∧
        ∀ i, ψ i ≫ pZ = pullback.fst _ _ ≫ pB ∧ j ≫ ψ i = φ i := by sorry
