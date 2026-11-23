-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_add
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:00.644896+00:00
-- url     : https://prove2.me/theorems/f84a4496-7e6b-4575-99e6-ecfc5d0fdb7b
-- title:
--   Coset Step: loc Mem add
-- statement:
--   The Coset Step construction uses the loc Mem add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L48-L55

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

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_add {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : LocMem I w a) (hb : LocMem I w b) : LocMem I w (a + b) := by sorry
