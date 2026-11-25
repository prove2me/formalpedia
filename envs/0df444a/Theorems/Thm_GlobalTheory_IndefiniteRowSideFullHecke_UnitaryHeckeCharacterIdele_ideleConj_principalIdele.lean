-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_ideleConj_principalIdele
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:00.914801+00:00
-- url     : https://prove2.me/theorems/e2865c8c-4011-4576-896b-b93575ba7236
-- title:
--   Unitary Hecke Character Idele: idele Conj principal Idele
-- statement:
--   The Unitary Hecke Character Idele construction uses the idele Conj principal Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L222-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L222-L228

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] (x : Eˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj F E (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E x) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E
        (Units.map (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E).toRingEquiv.toRingHom.toMonoidHom x) := by sorry
