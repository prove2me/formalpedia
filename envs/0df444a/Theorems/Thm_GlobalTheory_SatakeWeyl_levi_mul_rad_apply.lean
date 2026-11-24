-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_levi_mul_rad_apply
-- name    : GlobalTheory.SatakeWeyl.levi_mul_rad_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:27:47.166972+00:00
-- url     : https://prove2.me/theorems/5f7f3a7a-ce1a-4cb0-836d-093ded0bca09
-- title:
--   Satake Weyl: levi mul rad apply
-- statement:
--   The Satake Weyl construction uses the levi mul rad apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryLeviNormalizesUnipotentRadical.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryLeviNormalizesUnipotentRadical.lean#L9-L20

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl

theorem GlobalTheory.SatakeWeyl.levi_mul_rad_apply {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n}
    (hm : ∀ i j, β i ≠ β j → mat m i j = 0)
    (hu : ∀ i j, β j ≤ β i → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j) {i l : Fin n} (h : β l ≤ β i) :
    mat (m * u) i l = mat m i l := by sorry
