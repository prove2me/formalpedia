-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_ht_U
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.ht_U
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:58:54.455524+00:00
-- url     : https://prove2.me/theorems/746175de-775a-4dd6-82a9-ce52a4320628
-- title:
--   Rg Eis Levi: ht U
-- statement:
--   The Rg Eis Levi construction uses the ht U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L292-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L292-L306

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

theorem GlobalTheory.CompanionTheory.RgEisLevi.ht_U (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.Good) (ε : ℤˣ) [T2Space (A.U ε ι)]
    (hK : IsCompact (A.uK ε ι : Set (A.U ε ι))) (s : Set ι) (hI : Iwa (A.uQ ε s) (A.uK ε ι))
    (p : A.U ε ι) (hp : p ∈ A.uQ ε s) (k : A.U ε ι) (hk : k ∈ A.uK ε ι) :
    A.uH ε s (p * k) = A.lg (bdet (Sum.inl '' s : Set (ι ⊕ ι)) p.1) := by sorry
