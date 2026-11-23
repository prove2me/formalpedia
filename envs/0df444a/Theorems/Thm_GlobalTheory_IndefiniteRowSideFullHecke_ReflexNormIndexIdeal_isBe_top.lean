-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ReflexNormIndexIdeal_isBe_top
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.isBe_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:35.240502+00:00
-- url     : https://prove2.me/theorems/dce15c4b-4b74-4afa-8a04-0e2af4dbbf02
-- title:
--   Reflex Norm Index Ideal: is Be top
-- statement:
--   The Reflex Norm Index Ideal construction uses the is Be top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ReflexNormIndexIdeal.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ReflexNormIndexIdeal.lean#L74-L77

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.isBe_top : IsBe Dw c ⊤ 1 := by sorry
