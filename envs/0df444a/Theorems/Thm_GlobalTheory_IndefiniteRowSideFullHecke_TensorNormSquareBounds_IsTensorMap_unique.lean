-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TensorNormSquareBounds_IsTensorMap_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds.IsTensorMap.unique
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:10.567288+00:00
-- url     : https://prove2.me/theorems/7dfb6962-370d-448e-ac56-74846d06aa4f
-- title:
--   Is Tensor Map: unique
-- statement:
--   The Is Tensor Map construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TensorNormBound.lean#L48-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TensorNormBound.lean#L48-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds
open Formalism.BasicNotions Formalism.L2.DIV
variable {ι : Type} [Fintype ι] {n n' : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds.IsTensorMap.unique {lam : ι → DomWeight n} {lam' : ι → DomWeight n'}
    {A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)} {T T' : VV ℂ lam →ₗ[ℂ] VV ℂ lam'}
    (h : IsTensorMap A T) (h' : IsTensorMap A T') : T = T' := by sorry
