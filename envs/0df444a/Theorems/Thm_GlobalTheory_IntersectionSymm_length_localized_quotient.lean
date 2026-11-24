-- Prove2me | Theorems.Thm_GlobalTheory_IntersectionSymm_length_localized_quotient
-- name    : GlobalTheory.IntersectionSymm.length_localized_quotient
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:24.596281+00:00
-- url     : https://prove2.me/theorems/73571636-7049-4a23-8662-6a4553e9e1cd
-- title:
--   Intersection Symm: length localized quotient
-- statement:
--   The Intersection Symm construction uses the length localized quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L84-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L84-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.IntersectionSymm

theorem GlobalTheory.IntersectionSymm.length_localized_quotient {A : Type} [CommRing A] (p : Ideal A) [p.IsPrime] (a : A) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (A ⧸ Ideal.span {a})) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap A (Localization.AtPrime p) a}) := by sorry
