-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_hermMod_add
-- name    : GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:57.252414+00:00
-- url     : https://prove2.me/theorems/ae349967-a577-4472-ae19-2884cc5370db
-- title:
--   Herm Orth: herm Mod add
-- statement:
--   The Herm Orth construction uses the herm Mod add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L67-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L67-L77

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.HermOrth
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_add {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a b : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k)
    (hb : b ∈ hermMod σ ϖ n k) : a + b ∈ hermMod σ ϖ n k := by sorry
