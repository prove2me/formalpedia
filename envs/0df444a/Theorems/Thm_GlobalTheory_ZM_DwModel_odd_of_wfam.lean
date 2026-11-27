-- Prove2me | Theorems.Thm_GlobalTheory_ZM_DwModel_odd_of_wfam
-- name    : GlobalTheory.ZM.DwModel.odd_of_wfam
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:37.859554+00:00
-- url     : https://prove2.me/theorems/ea9985d3-dc9c-508a-be90-f1e18c66d75a
-- title:
--   Dw Model: odd of wfam
-- statement:
--   The Dw Model construction uses the odd of wfam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L119-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L119-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel

theorem GlobalTheory.ZM.DwModel.odd_of_wfam {o : Type} [CommRing o] {g : ℕ} {J : Type} {n N' : ℕ} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (W : WFam n em C Mat κ) : Odd N' := by sorry
