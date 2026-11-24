-- Prove2me | Theorems.Thm_GlobalTheory_CoefTorusWeight_detTwK_ne_zero
-- name    : GlobalTheory.CoefTorusWeight.detTwK_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:15:44.033794+00:00
-- url     : https://prove2.me/theorems/ca3866e6-2803-4ed7-aaac-58652777d11b
-- title:
--   Coef Torus Weight: det Tw K ne zero
-- statement:
--   The Coef Torus Weight construction uses the det Tw K ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceEndomorphismPreservesTorusWei.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceEndomorphismPreservesTorusWei.lean#L49-L51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWei
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
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
open GlobalTheory GlobalTheory.CoefTorusWeight

theorem GlobalTheory.CoefTorusWeight.detTwK_ne_zero {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) : detTwK lam h ≠ 0 := by sorry
