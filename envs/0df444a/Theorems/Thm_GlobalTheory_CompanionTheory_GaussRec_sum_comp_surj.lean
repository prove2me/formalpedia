-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_sum_comp_surj
-- name    : GlobalTheory.CompanionTheory.GaussRec.sum_comp_surj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:41.010372+00:00
-- url     : https://prove2.me/theorems/9cfeada7-c7d2-484d-b0fd-e91a4e064d4c
-- title:
--   Gauss Rec: sum comp surj
-- statement:
--   The Gauss Rec construction uses the sum comp surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L14-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L14-L43

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussRec
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.GaussRec.sum_comp_surj {A B : Type} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (π : A →+ B) (hπ : Function.Surjective π) (c : ℕ)
    (hc : Fintype.card A = c * Fintype.card B) (G : B → ℂ) :
    ∑ x, G (π x) = (c : ℂ) * ∑ y, G y := by sorry
