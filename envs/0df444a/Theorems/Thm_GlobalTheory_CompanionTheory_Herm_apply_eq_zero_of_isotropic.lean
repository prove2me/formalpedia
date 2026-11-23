-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Herm_apply_eq_zero_of_isotropic
-- name    : GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:05.041811+00:00
-- url     : https://prove2.me/theorems/5ecd27af-f9ab-48e5-806a-c67537a7b8a0
-- title:
--   Herm: apply eq zero of isotropic
-- statement:
--   The Herm construction uses the apply eq zero of isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianSemidefiniteNullRadical.lean#L7-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianSemidefiniteNullRadical.lean#L7-L53

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSemidefiniteNullRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Herm

theorem GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hs : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hp : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 := by sorry
