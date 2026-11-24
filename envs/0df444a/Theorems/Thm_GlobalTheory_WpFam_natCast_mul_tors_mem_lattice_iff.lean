-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_natCast_mul_tors_mem_lattice_iff
-- name    : GlobalTheory.WpFam.natCast_mul_tors_mem_lattice_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:15.733343+00:00
-- url     : https://prove2.me/theorems/2560dd12-b20f-4dad-b597-aef66f5875a9
-- title:
--   Wp Fam: nat Cast mul tors mem lattice iff
-- statement:
--   The Wp Fam construction uses the nat Cast mul tors mem lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCastMulTorsMemLatticeIff.lean#L13-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCastMulTorsMemLatticeIff.lean#L13-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastMulTorsMemLatticeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam

theorem GlobalTheory.WpFam.natCast_mul_tors_mem_lattice_iff :
    ∀ (N : ℕ) [NeZero N] (τ : ℍ) (M : ℕ) (x : Fin 2 → ZMod N),
      (M : ℂ) * tors N τ x ∈ (tauPair τ).lattice ↔ M • x = 0 := by sorry
