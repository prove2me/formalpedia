-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ReflexNormIndexIdeal_be_spec
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.be_spec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:48.479873+00:00
-- url     : https://prove2.me/theorems/a9752440-2c5b-4c82-b4e8-701e0dee1150
-- title:
--   Reflex Norm Index Ideal: be spec
-- statement:
--   The Reflex Norm Index Ideal construction uses the be spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ReflexNormIndexIdeal.lean#L94-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ReflexNormIndexIdeal.lean#L94-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
variable {Dw c}

theorem GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.be_spec (hK : ReflexLe Dw c) (Λ : Lat E n) : IsBeLat Dw c Λ (be hK Λ) := by sorry
