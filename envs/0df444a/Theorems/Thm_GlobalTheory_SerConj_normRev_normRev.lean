-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_normRev_normRev
-- name    : GlobalTheory.SerConj.normRev_normRev
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:41.255537+00:00
-- url     : https://prove2.me/theorems/48e8b127-8625-49d2-a848-5580164bb792
-- title:
--   Ser Conj: norm Rev norm Rev
-- statement:
--   The Ser Conj construction uses the norm Rev norm Rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L166-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L166-L174

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
variable {K : Type} [Field K]

theorem GlobalTheory.SerConj.normRev_normRev {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    C ((C (f.coeff 0)⁻¹ * f.reverse).coeff 0)⁻¹ * (C (f.coeff 0)⁻¹ * f.reverse).reverse = f := by sorry
