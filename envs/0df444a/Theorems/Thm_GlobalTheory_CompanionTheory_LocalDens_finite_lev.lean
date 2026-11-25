-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_finite_lev
-- name    : GlobalTheory.CompanionTheory.LocalDens.finite_lev
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:56.682421+00:00
-- url     : https://prove2.me/theorems/e4fabf41-9599-44f5-a348-23837ccb8e36
-- title:
--   Local Dens: finite lev
-- statement:
--   The Local Dens construction uses the finite lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L74-L77

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.LocalDens.finite_lev {ϖ : R} (h : Finite (R ⧸ lev ϖ 1)) (k : ℕ) : Finite (R ⧸ lev ϖ k) := by sorry
