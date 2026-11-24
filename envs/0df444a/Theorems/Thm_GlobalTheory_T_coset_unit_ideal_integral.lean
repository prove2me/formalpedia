-- Prove2me | Theorems.Thm_GlobalTheory_T_coset_unit_ideal_integral
-- name    : GlobalTheory.T.coset_unit_ideal_integral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:08.188619+00:00
-- url     : https://prove2.me/theorems/59fe3506-aa15-44a9-b1f1-b16e830904a2
-- title:
--   T: coset unit ideal integral
-- statement:
--   The T construction uses the coset unit ideal integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetUnitIdealIntegralStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetUnitIdealIntegralStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetUnitIdealIntegral
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetUnitIdealIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.coset_unit_ideal_integral : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by sorry
