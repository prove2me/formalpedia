-- Prove2me | Theorems.Thm_GlobalTheory_PadicComplexHost_isPrecomplete
-- name    : GlobalTheory.PadicComplexHost.isPrecomplete
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:42:34.721213+00:00
-- url     : https://prove2.me/theorems/409e66d9-02bf-4eee-aaf4-8343f16ac7ec
-- title:
--   Padic Complex Host: is Precomplete
-- statement:
--   The Padic Complex Host construction uses the is Precomplete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L56-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L56-L72

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

theorem GlobalTheory.PadicComplexHost.isPrecomplete : IsPrecomplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by sorry
