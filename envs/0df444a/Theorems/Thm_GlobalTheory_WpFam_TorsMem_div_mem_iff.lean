-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_TorsMem_div_mem_iff
-- name    : GlobalTheory.WpFam.TorsMem.div_mem_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:55:51.474587+00:00
-- url     : https://prove2.me/theorems/c6c721c5-559f-42cb-8bc1-0d7c76e94497
-- title:
--   Tors Mem: div mem iff
-- statement:
--   The Tors Mem construction uses the div mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionPointOfLatticeTauLatticeMembership.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionPointOfLatticeTauLatticeMembership.lean#L31-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointOfLatticeTauLatticeMembership
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
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.TorsMem

theorem GlobalTheory.WpFam.TorsMem.div_mem_iff (N : ℕ) [NeZero N] (τ : ℍ) (u v : ℤ) :
    ((u : ℂ) * τ + (v : ℂ)) / N ∈ (tauPair τ).lattice ↔ (u : ZMod N) = 0 ∧ (v : ZMod N) = 0 := by sorry
