-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Congruence_finite_quotient_span_pow
-- name    : GlobalTheory.CompanionTheory.Congruence.finite_quotient_span_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:47:56.76942+00:00
-- url     : https://prove2.me/theorems/b2dc176d-0d4d-4946-a0ba-7c58dc50a255
-- title:
--   Congruence: finite quotient span pow
-- statement:
--   The Congruence construction uses the finite quotient span pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteCosetsPrincipalCongruence.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteCosetsPrincipalCongruence.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteCosetsPrincipalCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Congruence
open Matrix

theorem GlobalTheory.CompanionTheory.Congruence.finite_quotient_span_pow (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (ϖ : R) (m : ℕ) (hϖ : Irreducible ϖ) :
    Finite (R ⧸ Ideal.span {ϖ ^ m}) := by sorry
