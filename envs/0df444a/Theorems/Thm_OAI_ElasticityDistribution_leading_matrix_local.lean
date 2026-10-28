-- Prove2me | Theorems.Thm_OAI_ElasticityDistribution_leading_matrix_local
-- name    : OAI.ElasticityDistribution.leading_matrix_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:45:24.862923+00:00
-- url     : https://prove2.me/theorems/7f7a4d72-2979-4a65-95e7-d06504f05729
-- title:
--   OAI.ElasticityDistribution.leading_matrix_local: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityDistribution.leading_matrix_local` of [lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityDistribution`, with `open Set TemperedDistribution`, `open scoped SchwartzMap LineDeriv BigOperators`, `open ElasticityAugmented`):
--
--   ```lean
--   lemma leading_matrix_local {B : Set X} (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
--       (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1) (U : Fin 4 → Dist)
--       (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => U j.succ) (U 0) i) 0)
--       (hs : LocalEq B (leadingSd θ lam m (fun j => U j.succ) (U 0)) 0) (i : Fin 4) :
--       LocalEq B ((2 : ℂ) • directiond θ (U i)+
--         ∑ k,∑ j,θ k • (coeffA dc lam m n o k i j • U j)) 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.coeffA`, `OAI.ElasticityDistribution.Coeff`, `OAI.ElasticityDistribution.Dist` and `OAI.ElasticityDistribution.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityDistribution.LocalEq`, `OAI.ElasticityDistribution.dc`, `OAI.ElasticityDistribution.directiond` and `OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityDistribution.leadingRd` and `OAI.ElasticityDistribution.leadingSd` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proofs of `OAI_ElasticityDistribution_weak_leading_smooth` and `OAI.Elasticity.dn_smooth_transport_column` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean (declaration OAI.ElasticityDistribution.leading_matrix_local)

import Mathlib
import Definitions.Def_OAIQ6El006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open Set TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented

lemma leading_matrix_local {B : Set X} (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1) (U : Fin 4 → Dist)
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => U j.succ) (U 0) i) 0)
    (hs : LocalEq B (leadingSd θ lam m (fun j => U j.succ) (U 0)) 0) (i : Fin 4) :
    LocalEq B ((2 : ℂ) • directiond θ (U i)+
      ∑ k,∑ j,θ k • (coeffA dc lam m n o k i j • U j)) 0 := by
  sorry
end ElasticityDistribution
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end
