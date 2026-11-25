-- Prove2me | Theorems.Thm_GlobalTheory_ProjCoh_exists_basis_top
-- name    : GlobalTheory.ProjCoh.exists_basis_top
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:10.432529+00:00
-- url     : https://prove2.me/theorems/3e86dce6-a8df-43ba-9285-3369091bff2e
-- title:
--   Proj Coh: exists basis top
-- statement:
--   The Proj Coh construction uses the exists basis top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBasisPolyGrading.lean#L44-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBasisPolyGrading.lean#L44-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.ProjCoh
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]

theorem GlobalTheory.ProjCoh.exists_basis_top {κ : Type} (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) {N : ℕ} (hN : Fintype.card ι = N + 1 + 1) :
    ∃ c : Module.Basis {a : κ // T a = Finset.univ} R ((cechComplex A).homology (N + 1)),
      ∀ a, c a = topCech A hN (b Finset.univ ⟨a.1, Finset.subset_univ _⟩) := by sorry
