-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_hform_add_fst
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.hform_add_fst
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:03:10.63207+00:00
-- url     : https://prove2.me/theorems/8bd84f5e-a143-4fe7-9a73-ac0d68c99444
-- title:
--   Prim Carry: hform add fst
-- statement:
--   The Prim Carry construction uses the hform add fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HyperbolicPairUnitaryTransitive.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HyperbolicPairUnitaryTransitive.lean#L14-L19

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HyperbolicPairUnitaryTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
open GlobalTheory.CompanionTheory.SW.QuasiRefl
variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}

theorem GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.hform_add_fst (x x' y : Fin N → A) :
    hform τ H (x + x') y = hform τ H x y + hform τ H x' y := by sorry
