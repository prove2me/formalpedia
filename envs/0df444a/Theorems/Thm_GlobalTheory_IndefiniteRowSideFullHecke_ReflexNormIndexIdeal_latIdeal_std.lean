-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ReflexNormIndexIdeal_latIdeal_std
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.latIdeal_std
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:32.173162+00:00
-- url     : https://prove2.me/theorems/c25eb613-a1e1-4008-a22c-644422e03dfa
-- title:
--   Reflex Norm Index Ideal: lat Ideal std
-- statement:
--   The Reflex Norm Index Ideal construction uses the lat Ideal std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ReflexNormIndexIdeal.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ReflexNormIndexIdeal.lean#L45-L47

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
omit [IsCMField E]

theorem GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.latIdeal_std : latIdeal (Lat.std E n) = ⊤ := by sorry
