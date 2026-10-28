-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_stationary_lie_taylor_rms
-- name    : OAI.LogConcaveSampling.stationary_lie_taylor_rms
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:37:14.694179+00:00
-- url     : https://prove2.me/theorems/666ba9b6-cb2d-4280-b628-4dcd788185fe
-- title:
--   OAI.LogConcaveSampling.stationary_lie_taylor_rms: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.stationary_lie_taylor_rms` of [lean/OAI/Probability/LogConcave/Sampling/StationaryTensorVectorRms.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Sampling/StationaryTensorVectorRms.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling`, with `open MeasureTheory Set`, `open scoped Classical BigOperators NNReal`, `open TensorEnergy Quadrature`):
--
--   ```lean
--   theorem stationary_lie_taylor_rms {S : Type} [Fintype S] {d : ℕ}
--       {H : Point d → ℝ} (hH : PolySmooth H) (htail : HasGaussianLowerTail H)
--       [SFinite (gibbs H)] {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
--       (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
--       (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
--       (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
--         -A (Sum.elim (fun _ => z) (fun _ => i)) y)
--       (C D B : ℕ → ℝ) {α κ ρ : ℝ} (hκ : 0≤κ) (hρ : 1≤ρ) (hB : ∀k,0≤B k)
--       (hb : ∀k y,AllSplitBound (spatialTensor A (List.finRange k) y) (C k*α*ρ^k))
--       (hs : ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k*ρ^k))
--       (he : ∀k,0<k → spatialEnergy F k (gibbs H)≤κ*ρ^(2*k)*B k)
--       {s : Set ℝ} (Ψ : Point d → ℝ → Point d)
--       (hΨ : ∀y t,t∈s → HasDerivWithinAt (Ψ y) (skewLieField H A (Ψ y t)) s t)
--       (hm : Measurable (fun p : ℝ × Point d => Ψ p.2 p.1))
--       (hlaw : ∀t∈s,(gibbs H).map (fun y => Ψ y t)=gibbs H)
--       {a x : ℝ} (hax : a≤x) (hsub : uIcc a x⊆s) (n : ℕ) :
--       Integrable (fun y => ‖tensorVector F (Ψ y x)-chainTaylor
--         (fun k t => tensorVector (iterTensorLie H A F k) (Ψ y t)) n a x‖^2) (gibbs H) ∧
--       (∫y,‖tensorVector F (Ψ y x)-chainTaylor
--         (fun k t => tensorVector (iterTensorLie H A F k) (Ψ y t)) n a x‖^2 ∂gibbs H)≤
--         ((x-a)^(n+1)/(n.factorial:ℝ))^2*
--           (κ*(α^2*ρ^4)^(n+1)*iterEnergyBudget K C D B (n+1) 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.HasGaussianLowerTail` and `OAI.LogConcaveSampling.skewLieField` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.Quadrature.chainTaylor` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.PolySmooth`, `OAI.LogConcaveSampling.scoreField`, `OAI.LogConcaveSampling.spatialTensor` and `OAI.LogConcaveSampling.TensorEnergy.AllSplitBound` (definitions bundle `OAIQ048L002` of this split); `OAI.LogConcaveSampling.iterEnergyBudget`, `OAI.LogConcaveSampling.iterTensorLie` and `OAI.LogConcaveSampling.tensorVector` (definitions bundle `OAIQ048L003` of this split); `OAI.LogConcaveSampling.spatialEnergy` (definitions bundle `OAIQ048L004` of this split); `OAI.LogConcaveSampling.Point` and `OAI.LogConcaveSampling.gibbs` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proofs of `OAI.LogConcaveSampling.centeringMeanCircuit_rms`, `OAI.LogConcaveSampling.centeringPicard_state_rms`, `OAI.LogConcaveSampling.kernelActionPicard_rms` and `OAI.LogConcaveSampling.kernelCorrectionPicard_rms` of this split import it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Sampling/StationaryTensorVectorRms.lean (declaration OAI.LogConcaveSampling.stationary_lie_taylor_rms)

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
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped Classical BigOperators NNReal
open TensorEnergy Quadrature

theorem stationary_lie_taylor_rms {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (htail : HasGaussianLowerTail H)
    [SFinite (gibbs H)] {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    (C D B : ℕ → ℝ) {α κ ρ : ℝ} (hκ : 0≤κ) (hρ : 1≤ρ) (hB : ∀k,0≤B k)
    (hb : ∀k y,AllSplitBound (spatialTensor A (List.finRange k) y) (C k*α*ρ^k))
    (hs : ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k*ρ^k))
    (he : ∀k,0<k → spatialEnergy F k (gibbs H)≤κ*ρ^(2*k)*B k)
    {s : Set ℝ} (Ψ : Point d → ℝ → Point d)
    (hΨ : ∀y t,t∈s → HasDerivWithinAt (Ψ y) (skewLieField H A (Ψ y t)) s t)
    (hm : Measurable (fun p : ℝ × Point d => Ψ p.2 p.1))
    (hlaw : ∀t∈s,(gibbs H).map (fun y => Ψ y t)=gibbs H)
    {a x : ℝ} (hax : a≤x) (hsub : uIcc a x⊆s) (n : ℕ) :
    Integrable (fun y => ‖tensorVector F (Ψ y x)-chainTaylor
      (fun k t => tensorVector (iterTensorLie H A F k) (Ψ y t)) n a x‖^2) (gibbs H) ∧
    (∫y,‖tensorVector F (Ψ y x)-chainTaylor
      (fun k t => tensorVector (iterTensorLie H A F k) (Ψ y t)) n a x‖^2 ∂gibbs H)≤
      ((x-a)^(n+1)/(n.factorial:ℝ))^2*
        (κ*(α^2*ρ^4)^(n+1)*iterEnergyBudget K C D B (n+1) 0) := by
  sorry
end LogConcaveSampling

end

end

end

end OAI
end
