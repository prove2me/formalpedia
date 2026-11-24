-- Prove2me | Theorems.Thm_GlobalTheory_MaxOrder_exists_eq_uniformizer_smul
-- name    : GlobalTheory.MaxOrder.exists_eq_uniformizer_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:39.392121+00:00
-- url     : https://prove2.me/theorems/60798997-d397-488d-b223-9d382fdcb5d1
-- title:
--   Max Order: exists eq uniformizer smul
-- statement:
--   The Max Order construction uses the exists eq uniformizer smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralAevalEqAevalMapOfCoprimeCharpoly.lean#L12-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralAevalEqAevalMapOfCoprimeCharpoly.lean#L12-L72

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharpolyEqPowOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Matrix GlobalTheory.LatOrb IsLocalRing
open GlobalTheory GlobalTheory.MaxOrder

theorem GlobalTheory.MaxOrder.exists_eq_uniformizer_smul {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {n : ℕ} (P₀ : O[X])
    (hP : IsCoprime P₀ (derivative P₀)) (γ : Matrix (Fin n) (Fin n) K)
    (hγ : γ.charpoly = P₀.map (algebraMap O K)) (π : O) (hπ : Irreducible π)
    (y : Matrix (Fin n) (Fin n) K) (hy : IsIntegral O y) (N : ℕ) (hN : 1 ≤ N) (f : O[X])
    (hf : aeval γ f = π ^ N • y) : ∃ h : O[X], aeval γ f = π • aeval γ h := by sorry
