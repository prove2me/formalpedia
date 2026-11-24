-- Prove2me | Theorems.Thm_GlobalTheory_FormalAlg_map_comap_inf_sup_pow_eq
-- name    : GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:34:56.307894+00:00
-- url     : https://prove2.me/theorems/9e0d88fe-20cf-416e-acd3-6e61bcb4e6aa
-- title:
--   Formal Alg: map comap inf sup pow eq
-- statement:
--   The Formal Alg construction uses the map comap inf sup pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapInfSupPowEq.lean#L15-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapInfSupPowEq.lean#L15-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfSupPowEqOfTorsionArtinReesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrictStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapInfSupPowEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FormalAlg

theorem GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq : ∀ (W W' : Scheme.{0}) [IsAffine W] [IsLocallyNoetherian W] (π : W' ⟶ W)
    (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (K τ : W.IdealSheafData),
    (∀ x, x ∉ K.support → x ∈ U) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (τ.comap π).map π ⊓ (τ ⊔ K ^ k) = τ := by sorry
