-- Prove2me | Theorems.Thm_GlobalTheory_T_weylTensorCoefSpace_endomorphism_preserves_torus_weight
-- name    : GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:06.601024+00:00
-- url     : https://prove2.me/theorems/9ad93f08-01fa-45c9-b795-f6786ba96948
-- title:
--   T: weyl Tensor Coef Space endomorphism preserves torus weight
-- statement:
--   The T construction uses the weyl Tensor Coef Space endomorphism preserves torus weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceEndomorphismPreservesTorusWeiStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceEndomorphismPreservesTorusWeiStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWei
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWeiStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : Module.End K (VV K lam)), (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∀ v : VV K lam, (∀ m ∈ (v : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) → ∀ m ∈ ((g v : VV K lam) : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a := by sorry
