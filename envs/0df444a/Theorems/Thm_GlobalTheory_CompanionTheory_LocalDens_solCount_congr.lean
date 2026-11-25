-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_solCount_congr
-- name    : GlobalTheory.CompanionTheory.LocalDens.solCount_congr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:41.753503+00:00
-- url     : https://prove2.me/theorems/cc52f8a7-d51b-5229-aad3-7ab24c2e2512
-- title:
--   Local Dens: sol Count congr
-- statement:
--   The Local Dens construction uses the sol Count congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L117-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L117-L152

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

theorem GlobalTheory.CompanionTheory.LocalDens.solCount_congr {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (T g h : Matrix (Fin n) (Fin n) R) (k : ℕ) (hgh : red ϖ k (g * h) = 1) (hhg : red ϖ k (h * g) = 1) :
    solCount σ ϖ S (cT σ g * T * g) k = solCount σ ϖ S T k := by sorry
