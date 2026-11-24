-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_normRev_prod
-- name    : GlobalTheory.SerConj.normRev_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:36.794804+00:00
-- url     : https://prove2.me/theorems/8ac6a81e-6702-440b-9e61-566f64921c30
-- title:
--   Ser Conj: norm Rev prod
-- statement:
--   The Ser Conj construction uses the norm Rev prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L157-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L157-L164

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

theorem GlobalTheory.SerConj.normRev_prod {α : Type} (s : Finset α) (P : α → K[X]) :
    C ((∏ c ∈ s, P c).coeff 0)⁻¹ * (∏ c ∈ s, P c).reverse = ∏ c ∈ s, C ((P c).coeff 0)⁻¹ * (P c).reverse := by sorry
