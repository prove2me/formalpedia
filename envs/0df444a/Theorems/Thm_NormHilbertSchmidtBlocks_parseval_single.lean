-- Prove2me | Theorems.Thm_NormHilbertSchmidtBlocks_parseval_single
-- name    : NormHilbertSchmidtBlocks.parseval_single
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:54.504676+00:00
-- url     : https://prove2.me/theorems/236aed12-5252-49fb-8d6d-ceca516712b6
-- title:
--   Norm Hilbert Schmidt Blocks: parseval single
-- statement:
--   The Norm Hilbert Schmidt Blocks construction uses the parseval single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HilbertSchmidtBlocks/Change.lean#L31-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HilbertSchmidtBlocks/Change.lean#L31-L56

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_Change
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open NormHilbertSchmidtBlocks

theorem NormHilbertSchmidtBlocks.parseval_single {C' V' : Type*} [Fintype C'] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (x y : PiLp 2 (fun _ : C' => V')) :
    ∑ p : (Σ _ : C', Fin (Module.finrank ℂ V')),
      inner ℂ x (WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V')) *
      inner ℂ (WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V')) y =
      inner ℂ x y := by sorry
