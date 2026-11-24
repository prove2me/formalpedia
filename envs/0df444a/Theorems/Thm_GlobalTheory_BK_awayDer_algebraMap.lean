-- Prove2me | Theorems.Thm_GlobalTheory_BK_awayDer_algebraMap
-- name    : GlobalTheory.BK.awayDer_algebraMap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:48.632138+00:00
-- url     : https://prove2.me/theorems/f0504c57-9911-4cbb-ba9b-afe525b3bbd7
-- title:
--   BK: away Der algebra Map
-- statement:
--   The BK construction uses the away Der algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L197-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L197-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable {A' B : Type} [CommRing A'] [CommRing B] (ι : A' →+* B) (s : A')
variable {ι s}
variable {k : Type} [CommRing k] [Algebra k A'] (I : Ideal A') (D : Derivation k A' A')

theorem GlobalTheory.BK.awayDer_algebraMap (s r : A') :
    awayDer D s (algebraMap A' _ r) = algebraMap A' _ (D r) := by sorry
