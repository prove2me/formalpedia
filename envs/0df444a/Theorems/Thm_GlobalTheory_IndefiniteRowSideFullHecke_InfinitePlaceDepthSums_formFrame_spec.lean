-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InfinitePlaceDepthSums_formFrame_spec
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums.formFrame_spec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:37.363804+00:00
-- url     : https://prove2.me/theorems/841e6e15-8287-4f2c-9cf3-fd3df52b1202
-- title:
--   Infinite Place Depth Sums: form Frame spec
-- statement:
--   The Infinite Place Depth Sums construction uses the form Frame spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/InfinitePlaceDepthSums.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/InfinitePlaceDepthSums.lean#L35-L50

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_InfinitePlaceDepthSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums

theorem GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums.formFrame_spec {K : Type} [Field K] [NumberField K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    IsUnit (formFrame H v).det ∧
      ((formFrame H v)⁻¹).conjTranspose * (formFrame H v)⁻¹ = H.map v.embedding := by sorry
