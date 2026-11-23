-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_conj_conj
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:46.519906+00:00
-- url     : https://prove2.me/theorems/908b24da-94cb-4e11-921b-b4949b491f8c
-- title:
--   Unitary Hecke Character Idele: conj conj
-- statement:
--   The Unitary Hecke Character Idele construction uses the conj conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L58-L61

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj_conj [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] (x : E) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E x) = x := by sorry
