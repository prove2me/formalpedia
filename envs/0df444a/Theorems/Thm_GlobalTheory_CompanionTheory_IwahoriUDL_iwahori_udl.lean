-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_iwahori_udl
-- name    : GlobalTheory.CompanionTheory.IwahoriUDL.iwahori_udl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:52.172709+00:00
-- url     : https://prove2.me/theorems/8615b0cc-2c62-42fa-8bb9-28014c62bc3a
-- title:
--   Iwahori UDL: iwahori udl
-- statement:
--   The Iwahori UDL construction uses the iwahori udl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L210-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L210-L232

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwahoriUDL
open Matrix
variable {R : Type*} [CommRing R]

theorem GlobalTheory.CompanionTheory.IwahoriUDL.iwahori_udl : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ)
    (ϖ : R) (m : ℕ), Irreducible ϖ → 1 ≤ m → ∀ g : Matrix (Fin n) (Fin n) R,
    (∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) →
    ∃ (u d l : Matrix (Fin n) (Fin n) R),
      (∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, d i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, l i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧ (∀ i j, i ≠ j → d i j = 0) ∧
      (∀ i j, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧ g = u * d * l := by sorry
