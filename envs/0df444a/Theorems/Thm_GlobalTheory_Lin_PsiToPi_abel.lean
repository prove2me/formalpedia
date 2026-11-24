-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_abel
-- name    : GlobalTheory.Lin.PsiToPi.abel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:06:12.412166+00:00
-- url     : https://prove2.me/theorems/1b651fd4-a8bd-404e-8252-67da1400b479
-- title:
--   Psi To Pi: abel
-- statement:
--   The Psi To Pi construction uses the abel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L95-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L95-L114

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

theorem GlobalTheory.Lin.PsiToPi.abel (P : ℕ → Prop) {Y X : ℝ} (hY : 1 < Y) (hYX : Y ≤ X) :
    cnt P X - cnt P Y = (∑ k ∈ Finset.Icc 0 ⌊X⌋₊, wt P k) / Real.log X - (∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, wt P k) / Real.log Y +
      ∫ t in Y..X, 1 / (t * Real.log t ^ 2) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, wt P k := by sorry
