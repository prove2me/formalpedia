-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_v_iff
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_v_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:46.753005+00:00
-- url     : https://prove2.me/theorems/35f61f6f-52ea-463b-b9bc-0e7b5422ce7a
-- title:
--   Coset Step: loc Mem v iff
-- statement:
--   The Coset Step construction uses the loc Mem v iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L116-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L116-L173

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetStep
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_v_iff {I : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} (hI : ¬ I ≤ v.asIdeal) (k : ℕ)
    (t : F) : LocMem (I * v.asIdeal ^ k) v t ↔ v.valuation F t ≤ WithZero.exp (-(k : ℤ)) := by sorry
