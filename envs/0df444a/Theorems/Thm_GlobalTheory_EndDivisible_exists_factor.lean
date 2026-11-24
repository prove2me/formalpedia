-- Prove2me | Theorems.Thm_GlobalTheory_EndDivisible_exists_factor
-- name    : GlobalTheory.EndDivisible.exists_factor
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:58:47.567864+00:00
-- url     : https://prove2.me/theorems/a8cbecf3-6a2d-4098-b0a3-fa282e8b5829
-- title:
--   End Divisible: exists factor
-- statement:
--   The End Divisible construction uses the exists factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeOfSumEqZero.lean#L30-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeOfSumEqZero.lean#L30-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeOfSumEqZero
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
open GlobalTheory GlobalTheory.EndDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace

theorem GlobalTheory.EndDivisible.exists_factor {X W Y S : Scheme.{0}} [IsIntegral X] [Y.IsSeparated] [IsAffine S] (f : X ⟶ W)
    (w : W ⟶ Y) (g : X ⟶ S) (hS : IsField Γ(S, ⊤)) (D : W.Opens) (hD : IsAffineOpen D) (z : X) (hz : f z ∈ D)
    (h : ∀ a : Γ(W, D), ∃ c : Γ(S, ⊤), gs g z ⊤ c = gs f z D a) : ∃ p : S ⟶ Y, f ≫ w = g ≫ p := by sorry
