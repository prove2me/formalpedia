-- Prove2me | Theorems.Thm_GlobalTheory_SepAffInf_isAffineOpen_inf_of_le_preimage
-- name    : GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:24.372472+00:00
-- url     : https://prove2.me/theorems/15b2c8a1-330e-5842-83f6-894fb9150e93
-- title:
--   Sep Aff Inf: is Affine Open inf of le preimage
-- statement:
--   The Sep Aff Inf construction uses the is Affine Open inf of le preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineOpenInfOfSeparatedOverAffineOpen.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineOpenInfOfSeparatedOverAffineOpen.lean#L7-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineOpenInfOfSeparatedOverAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open GlobalTheory GlobalTheory.SepAffInf

theorem GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage {X Z : Scheme.{0}} (h : Z ⟶ X) [IsSeparated h]
    (U : X.affineOpens) (Ω₁ Ω₂ : Z.affineOpens)
    (h₁ : Ω₁.1 ≤ h ⁻¹ᵁ U.1) (h₂ : Ω₂.1 ≤ h ⁻¹ᵁ U.1) : IsAffineOpen (Ω₁.1 ⊓ Ω₂.1) := by sorry
