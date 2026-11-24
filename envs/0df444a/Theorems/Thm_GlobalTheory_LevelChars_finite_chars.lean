-- Prove2me | Theorems.Thm_GlobalTheory_LevelChars_finite_chars
-- name    : GlobalTheory.LevelChars.finite_chars
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:37.45645+00:00
-- url     : https://prove2.me/theorems/92372495-8080-4cc5-ab98-180df3487cf7
-- title:
--   Level Chars: finite chars
-- statement:
--   The Level Chars construction uses the finite chars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteChars.lean#L49-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteChars.lean#L49-L62

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteChars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LevelChars

theorem GlobalTheory.LevelChars.finite_chars {G : Type} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] :
    {ψ : G →* ℂˣ | H ≤ ψ.ker}.Finite := by sorry
