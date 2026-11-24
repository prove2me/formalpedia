-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_wallQ
-- name    : GlobalTheory.CompanionTheory.RgEis.wallQ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:21.68516+00:00
-- url     : https://prove2.me/theorems/947c87ac-2e1f-4705-bd84-dc95e0b3a7fe
-- title:
--   Rg Eis: wall Q
-- statement:
--   The Rg Eis construction uses the wall Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L37-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L37-L61

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
open Classical

theorem GlobalTheory.CompanionTheory.RgEis.wallQ (hTr : Transfer) (hTop : GrpTop) (hPar : ParLaw) (hLQ : LeviQ) (A : Ad E R) (hA : A.Good) (ε : ℤˣ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Set ι) (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι))
    (hSg : A.Sg ε (sᶜ : Set ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasWall (A.uΓ ε ι ⊓ A.uQ ε s) (A.uK ε ι) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uC ε ι)
      (fun g => A.uH ε Set.univ g - A.uH ε s g) (fun g => A.uH ε Set.univ g - A.uH ε s g)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g)) ρ := by sorry
