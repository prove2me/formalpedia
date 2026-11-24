-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_iwa_inf
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.iwa_inf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:58:27.490424+00:00
-- url     : https://prove2.me/theorems/073d7155-3504-47ab-879d-fb09b3278884
-- title:
--   Rg Eis Levi: iwa inf
-- statement:
--   The Rg Eis Levi construction uses the iwa inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L268-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L268-L277

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
variable [TopologicalSpace R]

theorem GlobalTheory.CompanionTheory.RgEisLevi.iwa_inf (A : Ad E R) (hA : A.Good) (ε : ℤˣ) (hI : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι)) (s : Set ι) :
    Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι) := by sorry
