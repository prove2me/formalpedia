-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LinCount_gsum_lin_cast
-- name    : GlobalTheory.PMonE.LinCount.gsum_lin_cast
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:40:01.157402+00:00
-- url     : https://prove2.me/theorems/400369f2-9413-4dff-90b6-87ffd79b87df
-- title:
--   Lin Count: gsum lin cast
-- statement:
--   The Lin Count construction uses the gsum lin cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L98-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LinCount
open Finset GlobalTheory.PMonE
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

theorem GlobalTheory.PMonE.LinCount.gsum_lin_cast (q K E : ℕ) (M : ℕ → Matrix m m F) (X : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    gsum q (E + 1) (lin K M) X (i.castSucc, a) = X (i.castSucc, a) ^ q - X (i.succ, a) := by sorry
