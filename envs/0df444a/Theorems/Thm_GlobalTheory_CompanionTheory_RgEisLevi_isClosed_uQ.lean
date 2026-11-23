-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_isClosed_uQ
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.isClosed_uQ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:27.478236+00:00
-- url     : https://prove2.me/theorems/63ffd98d-cc31-4c65-98fc-dc57c72e2850
-- title:
--   Rg Eis Levi: is Closed u Q
-- statement:
--   The Rg Eis Levi construction uses the is Closed u Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L247-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L247-L250

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
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.RgEisLevi.isClosed_uQ (A : Ad E R) (ε : ℤˣ) (s : Set ι)
    (h : IsClosed (stab R (Sum.inl '' s : Set (ι ⊕ ι)) : Set (GL (ι ⊕ ι) R))) :
    IsClosed (A.uQ ε s : Set (A.U ε ι)) := by sorry
