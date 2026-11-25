-- Prove2me | Theorems.Thm_GlobalTheory_NormaliserCutBound_qC_re
-- name    : GlobalTheory.NormaliserCutBound.qC_re
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:06:05.613209+00:00
-- url     : https://prove2.me/theorems/a70010dd-7d52-5040-922e-ce5970546a14
-- title:
--   Normaliser Cut Bound: q C re
-- statement:
--   The Normaliser Cut Bound construction uses the q C re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdFinEqProdIcc.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdFinEqProdIcc.lean#L18-L24

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TwoBracketsLePowMulProdEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdFinEqProdIcc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open GlobalTheory GlobalTheory.NormaliserCutBound

theorem GlobalTheory.NormaliserCutBound.qC_re (P : M.Par) (y : ℝ) :
    (M.qC P (y : ℂ)).re = I.qpoly P.k P.T P.T' P.u P.u' y := by sorry
