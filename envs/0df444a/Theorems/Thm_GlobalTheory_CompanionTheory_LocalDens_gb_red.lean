-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_gb_red
-- name    : GlobalTheory.CompanionTheory.LocalDens.gb_red
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:18.913847+00:00
-- url     : https://prove2.me/theorems/e181dd72-04f1-424b-8a6f-b0e39065d965
-- title:
--   Local Dens: gb red
-- statement:
--   The Local Dens construction uses the gb red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L262-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L262-L264

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

theorem GlobalTheory.CompanionTheory.LocalDens.gb_red {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (k : ℕ)
    (x : Matrix (Fin m) (Fin n) R) : gb σ ϖ S k (red ϖ k x) = red ϖ k (gr σ S x) := by sorry
