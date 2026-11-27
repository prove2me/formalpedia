-- Prove2me | Theorems.Thm_GlobalTheory_JetProd_jetAt0_prod_rename
-- name    : GlobalTheory.JetProd.jetAt0_prod_rename
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:22:01.580898+00:00
-- url     : https://prove2.me/theorems/537613fa-300b-5a74-9571-6549030d7102
-- title:
--   Jet Prod: jet At0 prod rename
-- statement:
--   The Jet Prod construction uses the jet At0 prod rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/JetAt0ProdRename.lean#L194-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/JetAt0ProdRename.lean#L194-L217

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_JetAt0ProdRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.JetProd
open Finsupp
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ)
open scoped BigOperators
open NumberField
open Finsupp
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ)

theorem GlobalTheory.JetProd.jetAt0_prod_rename (hd : ∀ i j x y, e i x = e j y → i = j)
    (P : ∀ i, MvPolynomial (σ i) C) (G : ∀ i, MvPowerSeries (σ i) C) :
    _root_.Formalism.IncomingBounds.jetAt0 (∏ j, MvPolynomial.rename (e j) (P j)) (∏ j, MvPowerSeries.rename (e j) (G j)) =
      ∏ j, _root_.Formalism.IncomingBounds.jetAt0 (P j) (G j) := by sorry
