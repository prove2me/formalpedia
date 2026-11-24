-- Prove2me | Theorems.Thm_GlobalTheory_CubeTop_span_topClass
-- name    : GlobalTheory.CubeTop.span_topClass
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:23.025829+00:00
-- url     : https://prove2.me/theorems/9a6ec434-6cfb-44f6-b491-184ebae07990
-- title:
--   Cube Top: span top Class
-- statement:
--   The Cube Top construction uses the span top Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/TopClassSurjective.lean#L84-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/TopClassSurjective.lean#L84-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.CubeTop
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]

theorem GlobalTheory.CubeTop.span_topClass {κ : Type} (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) :
    Submodule.span R ((fun a : κ => topClass A (b Finset.univ ⟨a, Finset.subset_univ _⟩)) ''
      {a | T a = Finset.univ}) = ⊤ := by sorry
