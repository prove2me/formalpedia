-- Prove2me | Theorems.Thm_GlobalTheory_TateFree_comp_ofId_bijective
-- name    : GlobalTheory.TateFree.comp_ofId_bijective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:53:01.377531+00:00
-- url     : https://prove2.me/theorems/fa975939-78f5-4f78-995b-42b7c5bcc714
-- title:
--   Tate Free: comp of Id bijective
-- statement:
--   The Tate Free construction uses the comp of Id bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L35-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.TateFree
variable (O C A : Type) [CommRing O] [Field C] [Algebra O C] [IsIntegrallyClosedIn O C]
  [CommRing A]

theorem GlobalTheory.TateFree.comp_ofId_bijective [Algebra O A] [Module.Finite O A] :
    Function.Bijective fun x : A →ₐ[O] O => (Algebra.ofId O C).comp x := by sorry
