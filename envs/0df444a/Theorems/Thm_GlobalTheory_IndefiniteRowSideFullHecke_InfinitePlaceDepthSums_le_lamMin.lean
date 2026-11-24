-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InfinitePlaceDepthSums_le_lamMin
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums.le_lamMin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:12.150547+00:00
-- url     : https://prove2.me/theorems/6d16c656-ddf3-4f1c-ae17-b88c2c15f08e
-- title:
--   Infinite Place Depth Sums: le lam Min
-- statement:
--   The Infinite Place Depth Sums construction uses the le lam Min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/InfinitePlaceDepthSums.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/InfinitePlaceDepthSums.lean#L130-L134

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
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

theorem GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums.le_lamMin (hW : Df.WF) (S : IndefRows Df) (v : InfinitePlace K) (c : ℝ)
    (h : ∀ p, Df.Qp Bs.μ0 p ≠ ⊥ → c ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) : c ≤ lamMin hW S v := by sorry
