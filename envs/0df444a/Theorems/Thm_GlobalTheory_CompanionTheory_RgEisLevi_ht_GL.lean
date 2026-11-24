-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_ht_GL
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.ht_GL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:58:44.954722+00:00
-- url     : https://prove2.me/theorems/980194f2-d8af-42e8-8266-2aa8849a6b49
-- title:
--   Rg Eis Levi: ht GL
-- statement:
--   The Rg Eis Levi construction uses the ht GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L285-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L285-L290

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
variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]

theorem GlobalTheory.CompanionTheory.RgEisLevi.ht_GL (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.Good) (s : Set ι) (p : GL ι R) (hp : p ∈ stab R s)
    (k : GL ι R) (hk : k ∈ A.kGL ι) : A.htGL s (p * k) = A.lg (bdet s p) := by sorry
