-- Prove2me | Theorems.Thm_MassDataIdxStIm_midEmb_inj
-- name    : MassDataIdxStIm.midEmb_inj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:02.079804+00:00
-- url     : https://prove2.me/theorems/32f4a1e6-9376-4bc6-a890-31a9ebc88e9c
-- title:
--   Mass Data Idx St Im: mid Emb inj
-- statement:
--   The Mass Data Idx St Im construction uses the mid Emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/LeviEmbeddingBlock32.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/LeviEmbeddingBlock32.lean#L79-L79

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open MassDataIdxStIm
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]

theorem MassDataIdxStIm.midEmb_inj {h h' : Matrix (Fin k) (Fin k) A} (e : midEmb h = midEmb h') : h = h' := by sorry
