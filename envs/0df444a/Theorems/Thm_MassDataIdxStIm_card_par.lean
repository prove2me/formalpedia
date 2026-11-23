-- Prove2me | Theorems.Thm_MassDataIdxStIm_card_par
-- name    : MassDataIdxStIm.card_par
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:13.228052+00:00
-- url     : https://prove2.me/theorems/e402cc2b-ea03-4cbd-a16e-dc5bd5a71019
-- title:
--   Mass Data Idx St Im: card par
-- statement:
--   The Mass Data Idx St Im construction uses the card par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/Block31OfBlocks.lean#L193-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/Block31OfBlocks.lean#L193-L205

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Block31OfBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open MassDataIdxStIm
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]
variable {r k : ℕ}

theorem MassDataIdxStIm.card_par (K : Type) [Field K] [Fintype K] (r k : ℕ) (P : Matrix (Fin k) (Fin k) K → Prop) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // Par P x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // P h} *
        Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by sorry
