-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_tprod_eq_prod_mul_tprod_compl
-- name    : GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_eq_prod_mul_tprod_compl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:06.881581+00:00
-- url     : https://prove2.me/theorems/9491fdf5-87f0-4390-8798-02fbce04e731
-- title:
--   Abs Tprod: tprod eq prod mul tprod compl
-- statement:
--   The Abs Tprod construction uses the tprod eq prod mul tprod compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L26-L37

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AbsTprod

theorem GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_eq_prod_mul_tprod_compl {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (S : Finset ι) :
    Multipliable (fun v : {v // v ∉ S} => a v.1) ∧
      ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1 := by sorry
