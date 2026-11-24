-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Casselman_exists_mem_inf_conj_of_isDom
-- name    : GlobalTheory.CompanionTheory.Casselman.exists_mem_inf_conj_of_isDom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:31:44.109992+00:00
-- url     : https://prove2.me/theorems/675395bd-45c1-4c39-ac8c-1b23e53ede2b
-- title:
--   Casselman: exists mem inf conj of is Dom
-- statement:
--   The Casselman construction uses the exists mem inf conj of is Dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsMemInfConjOfIsDom.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsMemInfConjOfIsDom.lean#L8-L24

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_StrictDominance_JointGeneralisedEigenvectors_IsJointGenEig
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsMemInfConjOfIsDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep PositivityTheory.SphericalProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Casselman

theorem GlobalTheory.CompanionTheory.Casselman.exists_mem_inf_conj_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∀ y ∈ D.J,
      ∃ a ∈ D.J ⊓ D.N, a⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by sorry
