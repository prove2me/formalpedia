-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ReflexNormIndexIdeal_beIdeal_spec
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.beIdeal_spec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:45.460057+00:00
-- url     : https://prove2.me/theorems/16d79457-2f11-4c3e-9846-f4fb6d20c35f
-- title:
--   Reflex Norm Index Ideal: be Ideal spec
-- statement:
--   The Reflex Norm Index Ideal construction uses the be Ideal spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ReflexNormIndexIdeal.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ReflexNormIndexIdeal.lean#L88-L92

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.beIdeal_spec (hK : ReflexLe Dw c) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : IsBe Dw c 𝔞 (beIdeal hK 𝔞 h𝔞) := by sorry
