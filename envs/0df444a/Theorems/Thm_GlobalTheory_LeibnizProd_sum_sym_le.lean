-- Prove2me | Theorems.Thm_GlobalTheory_LeibnizProd_sum_sym_le
-- name    : GlobalTheory.LeibnizProd.sum_sym_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:17.640116+00:00
-- url     : https://prove2.me/theorems/fa309534-aebb-42e1-8443-e23162571f1a
-- title:
--   Leibniz Prod: sum sym le
-- statement:
--   The Leibniz Prod construction uses the sum sym le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivProdCoordLeLeibniz.lean#L28-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivProdCoordLeLeibniz.lean#L28-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivProdCoordLeLeibniz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.LeibnizProd

theorem GlobalTheory.LeibnizProd.sum_sym_le {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (a : ι → ℕ → ℝ)
    (ha : ∀ i k, 0 ≤ a i k) :
    ∑ p ∈ (Finset.univ : Finset ι).sym n, ∏ j, a j ((p : Multiset ι).count j) ≤
      ∏ j, ∑ k ∈ Finset.range (n + 1), a j k := by sorry
