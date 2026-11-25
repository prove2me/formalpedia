-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Congruence_finite_cosets_principal_congruence
-- name    : GlobalTheory.CompanionTheory.Congruence.finite_cosets_principal_congruence
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:01:01.52982+00:00
-- url     : https://prove2.me/theorems/f403b4a1-1ce4-47c0-b393-24def1ecc3c2
-- title:
--   Congruence: finite cosets principal congruence
-- statement:
--   The Congruence construction uses the finite cosets principal congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteCosetsPrincipalCongruence.lean#L15-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteCosetsPrincipalCongruence.lean#L15-L54

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

theorem GlobalTheory.CompanionTheory.Congruence.finite_cosets_principal_congruence :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Finite (IsLocalRing.ResidueField R)] (n : ℕ) (ϖ : R) (m : ℕ), Irreducible ϖ →
      ∃ s : Finset (Matrix (Fin n) (Fin n) R), ∀ A : Matrix (Fin n) (Fin n) R, IsUnit A.det →
        ∃ g ∈ s, ∃ B : Matrix (Fin n) (Fin n) R, IsUnit g.det ∧
          (∀ i j, B i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
          A = g * B := by sorry
