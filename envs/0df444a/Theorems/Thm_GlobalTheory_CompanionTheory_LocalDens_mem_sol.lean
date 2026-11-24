-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_mem_sol
-- name    : GlobalTheory.CompanionTheory.LocalDens.mem_sol
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:52:16.530809+00:00
-- url     : https://prove2.me/theorems/85129388-cda9-4b88-89ea-fbecf3b8e648
-- title:
--   Local Dens: mem sol
-- statement:
--   The Local Dens construction uses the mem sol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L266-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L266-L274

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

theorem GlobalTheory.CompanionTheory.LocalDens.mem_sol {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (T : Matrix (Fin n) (Fin n) R) (k : ℕ) (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :
    y ∈ sol σ ϖ S T k ↔ gb σ ϖ S k y = red ϖ k T := by sorry
