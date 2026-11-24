-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_cnt_eq
-- name    : GlobalTheory.Lin.PsiToPi.cnt_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:43.162849+00:00
-- url     : https://prove2.me/theorems/bcaa1ed0-7b68-449d-91e7-f4137d49c47e
-- title:
--   Psi To Pi: cnt eq
-- statement:
--   The Psi To Pi construction uses the cnt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L84-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L84-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)

theorem GlobalTheory.Lin.PsiToPi.cnt_eq (P : ℕ → Prop) (u : ℝ) :
    cnt P u = ∑ k ∈ Finset.Ioc 0 ⌊u⌋₊, 1 / Real.log k * wt P k := by sorry
