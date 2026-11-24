-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_g_out
-- name    : GlobalTheory.HeckeTwo.Regroup.g_out
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:42.471661+00:00
-- url     : https://prove2.me/theorems/bc380c9c-69d0-45b9-b6f2-07184e2e6ecf
-- title:
--   Regroup: g out
-- statement:
--   The Regroup construction uses the g out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TsumLatticePairUnitQuotientRegroup.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TsumLatticePairUnitQuotientRegroup.lean#L87-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.Regroup
variable {F : Type} [Field F] [NumberField F]
variable (𝔞 𝔟 : Frac F)

theorem GlobalTheory.HeckeTwo.Regroup.g_out {g : F × F → ℂ}
    (hg : ∀ (ε : (𝓞 F)ˣ) (a b : F), g (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = g (a, b))
    (p : LatPair 𝔞 𝔟) : g (Quotient.mk (latRel 𝔞 𝔟) p).out.1 = g p.1 := by sorry
