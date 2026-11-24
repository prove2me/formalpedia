-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_wallsS
-- name    : GlobalTheory.CompanionTheory.RgEis.wallsS
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:23.171255+00:00
-- url     : https://prove2.me/theorems/fd9154e4-9978-4afd-b74f-c653ccd7d032
-- title:
--   Rg Eis: walls S
-- statement:
--   The Rg Eis construction uses the walls S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L63-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L63-L124

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

theorem GlobalTheory.CompanionTheory.RgEis.wallsS (hTr : Transfer) (hTw : Twist) (hTop : GrpTop) (hPar : ParLaw) (hLS : LeviS) (A : Ad E R) (hA : A.Good)
    (hMir : A.MirGL) (ε : ℤˣ) {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι) (hN : 2 ≤ Fintype.card ι)
    (hS : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasFirst (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)) ρ ∧
    HasWall (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uC ε ι) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g) (A.uH ε {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g) ρ ∧
    HasLast (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (A.uH ε Set.univ) (Fintype.card ι) ρ := by sorry
