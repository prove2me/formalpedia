-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_aeval_smul_of_isHomogeneous
-- name    : GlobalTheory.ChowHt.aeval_smul_of_isHomogeneous
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:16.032685+00:00
-- url     : https://prove2.me/theorems/78a84d7e-5ef6-4824-836b-82a03088afc3
-- title:
--   Chow Ht: aeval smul of is Homogeneous
-- statement:
--   The Chow Ht construction uses the aeval smul of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallAevalLineVanishingIdealIff.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallAevalLineVanishingIdealIff.lean#L19-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
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
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.ChowHt.aeval_smul_of_isHomogeneous {k K : Type} [Field k] [Field K] [Algebra k K] {N d : ℕ}
    {g : MvPolynomial (Fin N) k} (hg : g.IsHomogeneous d) (t : K) (z : Fin N → K) :
    aeval (t • z) g = t ^ d * aeval z g := by sorry
