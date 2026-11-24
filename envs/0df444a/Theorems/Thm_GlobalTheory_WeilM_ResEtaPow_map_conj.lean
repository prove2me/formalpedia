-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_ResEtaPow_map_conj
-- name    : GlobalTheory.WeilM.ResEtaPow.map_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:16.235041+00:00
-- url     : https://prove2.me/theorems/09a993e1-a157-4c8b-b86c-0b1cabc93508
-- title:
--   Res Eta Pow: map conj
-- statement:
--   The Res Eta Pow construction uses the map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L402-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L402-L408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
variable {c}

theorem GlobalTheory.WeilM.ResEtaPow.map_conj {ξ : E} (h : IsQuad c ξ) {K : Subgroup Rˣ} {χ : Eˣ →* Circle} {n : ℕ} (hχ : ResEtaPow K χ n)
    (z : Eˣ) : χ (Units.map (c : E →* E) z) = (χ z)⁻¹ := by sorry
