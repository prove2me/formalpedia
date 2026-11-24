-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_LatSum_prod_abs_emb
-- name    : GlobalTheory.HeckeTwo.LatSum.prod_abs_emb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:05:53.619117+00:00
-- url     : https://prove2.me/theorems/d31929fe-32fb-44e2-ac12-c4c92002a8d7
-- title:
--   Lat Sum: prod abs emb
-- statement:
--   The Lat Sum construction uses the prod abs emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHeckeBalancedLatticeDoubleSum.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHeckeBalancedLatticeDoubleSum.lean#L75-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
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
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.LatSum
variable {F : Type} [Field F] [NumberField F]
variable [IsTotallyReal F]

theorem GlobalTheory.HeckeTwo.LatSum.prod_abs_emb (x : F) : ∏ τ : Emb F, |τ x| = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by sorry
