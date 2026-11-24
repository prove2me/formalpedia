-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Cass_proj_mem_fixed_piN
-- name    : GlobalTheory.CompanionTheory.Cass.proj_mem_fixed_piN
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:31:42.541797+00:00
-- url     : https://prove2.me/theorems/d5aadcfc-2ccd-4e7e-83c5-c71e9300fbc5
-- title:
--   Cass: proj mem fixed pi N
-- statement:
--   The Cass construction uses the proj mem fixed pi N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProjMemFixedPiN.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProjMemFixedPiN.lean#L7-L14

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_StrictDominance_JointGeneralisedEigenvectors_IsJointGenEig
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProjMemFixedPiN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep PositivityTheory.SphericalProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cass

theorem GlobalTheory.CompanionTheory.Cass.proj_mem_fixed_piN (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (v : fixed π D.J) : D.proj π (v : V) ∈ fixed (D.piN π) D.JT := by sorry
