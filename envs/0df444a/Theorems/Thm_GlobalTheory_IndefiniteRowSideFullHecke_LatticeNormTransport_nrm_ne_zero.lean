-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LatticeNormTransport_nrm_ne_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.nrm_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:00.263801+00:00
-- url     : https://prove2.me/theorems/1e2e0324-f774-4caa-9165-e94ca33e3f33
-- title:
--   Lattice Norm Transport: nrm ne zero
-- statement:
--   The Lattice Norm Transport construction uses the nrm ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/LatticeNormTransport.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/LatticeNormTransport.lean#L100-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport

theorem GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.nrm_ne_zero {K : Type} [Field K] [NumberField K] (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by sorry
