-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_conj_ne_one
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj_ne_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:58.334013+00:00
-- url     : https://prove2.me/theorems/a7eb7f22-3226-4b53-9b7c-f34d457e04cd
-- title:
--   Unitary Hecke Character Idele: conj ne one
-- statement:
--   The Unitary Hecke Character Idele construction uses the conj ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L63-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj_ne_one [IsCMExtension F E] : conj F E ≠ 1 := by sorry
