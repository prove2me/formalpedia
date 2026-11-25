-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_hasProd_eulerFactor
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.hasProd_eulerFactor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:16.700302+00:00
-- url     : https://prove2.me/theorems/a95da79c-6513-453b-93b8-02f028b76ff7
-- title:
--   Unitary Hecke Char: has Prod euler Factor
-- statement:
--   The Unitary Hecke Char construction uses the has Prod euler Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L446-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L446-L448

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
variable {E : Type} [Field E] [NumberField E]
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.hasProd_eulerFactor (χ : UnitaryHeckeChar E) (s : {s : ℂ // 1 < s.re}) :
    HasProd (fun P => χ.eulerFactor P s) (χ.finiteL s) := by sorry
