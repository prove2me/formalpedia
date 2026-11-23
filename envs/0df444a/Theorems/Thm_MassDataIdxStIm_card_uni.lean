-- Prove2me | Theorems.Thm_MassDataIdxStIm_card_uni
-- name    : MassDataIdxStIm.card_uni
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:04.828802+00:00
-- url     : https://prove2.me/theorems/51820209-46af-4e19-8065-b65725a8e6bf
-- title:
--   Mass Data Idx St Im: card uni
-- statement:
--   The Mass Data Idx St Im construction uses the card uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/Block31OfBlocks.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/Block31OfBlocks.lean#L84-L86

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

theorem MassDataIdxStIm.card_uni (K : Type) [Field K] [Fintype K] (n : ℕ) :
    Nat.card {u : Matrix (Fin n) (Fin n) K // IsUpUni u} = Fintype.card K ^ (n * (n - 1) / 2) := by sorry
