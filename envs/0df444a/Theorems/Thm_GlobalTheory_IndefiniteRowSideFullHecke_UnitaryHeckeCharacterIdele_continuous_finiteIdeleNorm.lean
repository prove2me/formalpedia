-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_continuous_finiteIdeleNorm
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteIdeleNorm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:13.383509+00:00
-- url     : https://prove2.me/theorems/e347ea88-1f51-4e34-b843-bf1947f25402
-- title:
--   Unitary Hecke Character Idele: continuous finite Idele Norm
-- statement:
--   The Unitary Hecke Character Idele construction uses the continuous finite Idele Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L521-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean#L521-L545

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteIdeleNorm : Continuous (finiteIdeleNorm (E := E)) := by sorry
