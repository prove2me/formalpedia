-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_cT_smul
-- name    : GlobalTheory.CompanionTheory.LocalDens.cT_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:52:34.450518+00:00
-- url     : https://prove2.me/theorems/266a2c48-ada9-44bd-8b07-f7ea5ca2d72c
-- title:
--   Local Dens: c T smul
-- statement:
--   The Local Dens construction uses the c T smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L20-L22

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

theorem GlobalTheory.CompanionTheory.LocalDens.cT_smul (σ : R →+* R) {a b : ℕ} (r : R) (x : Matrix (Fin a) (Fin b) R) :
    cT σ (r • x) = σ r • cT σ x := by sorry
