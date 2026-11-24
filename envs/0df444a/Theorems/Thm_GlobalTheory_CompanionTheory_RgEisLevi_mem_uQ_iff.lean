-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_mem_uQ_iff
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.mem_uQ_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:03.732029+00:00
-- url     : https://prove2.me/theorems/f715db9e-efb7-4d84-a0bb-c86af34eba69
-- title:
--   Rg Eis Levi: mem u Q iff
-- statement:
--   The Rg Eis Levi construction uses the mem u Q iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L254-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L254-L256

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.RgEisLevi.mem_uQ_iff (A : Ad E R) (ε : ℤˣ) (s : Set ι) (q : A.uQ ε (Set.univ : Set ι)) :
    q.1 ∈ A.uQ ε s ↔ piQ A ε q ∈ stab R s := by sorry
