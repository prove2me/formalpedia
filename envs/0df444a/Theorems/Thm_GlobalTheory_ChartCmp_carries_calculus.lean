-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_carries_calculus
-- name    : GlobalTheory.ChartCmp.carries_calculus
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:06.062303+00:00
-- url     : https://prove2.me/theorems/2edf0e3e-6f40-58de-9b73-6d955e5e96cf
-- title:
--   Chart Cmp: carries calculus
-- statement:
--   The Chart Cmp construction uses the carries calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CarriesLinCombGeneratorCalculus.lean#L70-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CarriesLinCombGeneratorCalculus.lean#L70-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CarriesLinCombGeneratorCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp
open CarryCalc

theorem GlobalTheory.ChartCmp.carries_calculus : ∀ (X X' : Scheme.{0}) (L' : LB X') (L : LB X) (F : X' ⟶ X) [Mono F] (w : LB.Iso L' (L.pull F)), L'.IsLB → L.IsLB → w.IsGen → (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)), g.IsGen → ∃ g', g'.IsGen ∧ Carries L F w φ ε g g') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h', LB.SameSum φ ε φ' ε' → g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → (LB.Gen.Corr L' _ _ _ _ g h ↔ LB.Gen.Corr L _ _ _ _ g' h')) ∧ (∀ (Y Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g' (r : Z ⟶ Y) (g'' : LB.Gen (LB.LinComb L (fun k => (r ≫ φ k) ≫ F) ε)), g.IsGen → g'.IsGen → g''.IsGen → Carries L F w φ ε g g' → LB.Gen.Corr L _ _ _ _ g'' (LB.pullGen L _ _ g' r) → Carries L F w (fun k => r ≫ φ k) ε (LB.pullGen L' φ ε g r) g'') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h' (p : LB.Gen (LB.LinComb L (fun k => Sum.elim φ φ' k ≫ F) (Sum.elim ε ε'))), g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → p.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → LB.Gen.Corr L _ _ _ _ p (LB.mulGen L _ _ _ _ g' h') → Carries L F w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L' _ _ _ _ g h) p) ∧ (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g', Carries L F w φ ε g g' → Carries L F w φ (fun k => - ε k) (LB.invGen L' φ ε g) (LB.invGen L _ ε g')) := by sorry
