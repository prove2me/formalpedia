-- Prove2me | Theorems.Thm_GlobalTheory_PadicComplexHost_isHausdorff
-- name    : GlobalTheory.PadicComplexHost.isHausdorff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:50:10.338985+00:00
-- url     : https://prove2.me/theorems/8822e4f3-f712-481f-ac1e-a0847b4e6c78
-- title:
--   Padic Complex Host: is Hausdorff
-- statement:
--   The Padic Complex Host construction uses the is Hausdorff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L48-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal
open GlobalTheory GlobalTheory.PadicComplexHost
variable (p : ℕ) [hp : Fact p.Prime]

theorem GlobalTheory.PadicComplexHost.isHausdorff : IsHausdorff (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by sorry
