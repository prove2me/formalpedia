-- Prove2me | Theorems.Thm_GlobalTheory_T_generator_iso_extend_from_open_containing_charts
-- name    : GlobalTheory.T.generator_iso_extend_from_open_containing_charts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:40:58.934233+00:00
-- url     : https://prove2.me/theorems/0dbace06-9031-4dcc-94d4-b8295940f2e2
-- title:
--   T: generator iso extend from open containing charts
-- statement:
--   The T construction uses the generator iso extend from open containing charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorIsoExtendFromOpenContainingChartsStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorIsoExtendFromOpenContainingChartsStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorIsoExtendFromOpenContainingCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorIsoExtendFromOpenContainingChartsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.generator_iso_extend_from_open_containing_charts : ∀ (X Y : Scheme.{0}) (c : Y ⟶ X) [IsOpenImmersion c], (∀ N : LB X, (∀ a, N.U a ≤ c.opensRange) → (∃ t : (N.pull c).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen) ∧ ∀ M M' : LB X, (∀ a b, M.U a ⊓ M'.U b ≤ c.opensRange) → LBIso (M.pull c) (M'.pull c) → LBIso M M' := by sorry
