-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_centering_velocity_taylor_uniform
-- name    : OAI.LogConcaveSampling.centering_velocity_taylor_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:37:32.159859+00:00
-- url     : https://prove2.me/theorems/136331a3-652f-4e13-af1b-1977b809c533
-- title:
--   OAI.LogConcaveSampling.centering_velocity_taylor_uniform: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.centering_velocity_taylor_uniform` of [lean/OAI/Probability/LogConcave/Complexity/CenteringStateBudgetNonneg.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Complexity/CenteringStateBudgetNonneg.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling`, with `open Set MeasureTheory TensorEnergy Quadrature`, `open scoped Classical BigOperators NNReal RealInnerProductSpace`):
--
--   ```lean
--   theorem centering_velocity_taylor_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
--       (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
--       (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
--       (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) (hs : 0 < s)
--       (Ξ : Point (d+d) → ℝ → Point (d+d))
--       (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
--         (skewLieField (centeringPotential F x r T)
--           (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)) (Icc (0:ℝ) 1) t)
--       (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
--       (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
--         gibbs (centeringPotential F x r T)) :
--       let A := jointSkew (centeringKernel hF x hr hl hT0 hT1) s
--       let I := vectorArray (id : Point (d+d) → Point (d+d))
--       let J := fun k t y => tensorVector (iterTensorLie (centeringPotential F x r T) A I k) (Ξ y t)
--       ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
--         Integrable (fun y => ‖J 1 b y-chainTaylor (fun k t => J (k+1) t y) n a b‖^2)
--           (gibbs (centeringPotential F x r T)) ∧
--         (∫y,‖J 1 b y-chainTaylor (fun k t => J (k+1) t y) n a b‖^2
--           ∂gibbs (centeringPotential F x r T))≤
--         ((b-a)^(n+1)/(n.factorial:ℝ))^2*
--           (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.centeringKernel`, `OAI.LogConcaveSampling.centeringPotential`, `OAI.LogConcaveSampling.jointSkew` and `OAI.LogConcaveSampling.skewLieField` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.centeringStateBudgetNonnegDecidableEqUnit` and `OAI.LogConcaveSampling.Quadrature.chainTaylor` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.iterTensorLie`, `OAI.LogConcaveSampling.tensorVector` and `OAI.LogConcaveSampling.vectorArray` (definitions bundle `OAIQ048L003` of this split); `OAI.LogConcaveSampling.centeringStateBudget` (definitions bundle `OAIQ048L004` of this split); `OAI.LogConcaveSampling.Point` and `OAI.LogConcaveSampling.gibbs` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.centeringPicard_state_rms` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Complexity/CenteringStateBudgetNonneg.lean (declaration OAI.LogConcaveSampling.centering_velocity_taylor_uniform)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004

section

attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

attribute [local instance] OAI.LogConcaveSampling.centeringStateBudgetNonnegDecidableEqUnit
theorem centering_velocity_taylor_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) (hs : 0 < s)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) :
    let A := jointSkew (centeringKernel hF x hr hl hT0 hT1) s
    let I := vectorArray (id : Point (d+d) → Point (d+d))
    let J := fun k t y => tensorVector (iterTensorLie (centeringPotential F x r T) A I k) (Ξ y t)
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖J 1 b y-chainTaylor (fun k t => J (k+1) t y) n a b‖^2)
        (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖J 1 b y-chainTaylor (fun k t => J (k+1) t y) n a b‖^2
        ∂gibbs (centeringPotential F x r T))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2)) := by
  sorry
end LogConcaveSampling

end

end

end OAI
end
