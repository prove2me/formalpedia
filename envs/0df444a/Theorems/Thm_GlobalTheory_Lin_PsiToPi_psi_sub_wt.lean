-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_psi_sub_wt
-- name    : GlobalTheory.Lin.PsiToPi.psi_sub_wt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:06:20.296787+00:00
-- url     : https://prove2.me/theorems/5c19de9f-e111-43e7-9e21-0538ad6da675
-- title:
--   Psi To Pi: psi sub wt
-- statement:
--   The Psi To Pi construction uses the psi sub wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L147-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L147-L156

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

theorem GlobalTheory.Lin.PsiToPi.psi_sub_wt (P : ℕ → Prop) {u : ℝ} (hu : 1 ≤ u) :
    |(∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k| ≤ 2 * √u * Real.log u := by sorry
