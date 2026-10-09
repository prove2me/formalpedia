-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentAmplificationErrorEnergy_finite_original_error_energy
-- name    : OAI.SevenEighths.CenteredMomentAmplificationErrorEnergy.finite_original_error_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:17:07.869444+00:00
-- url     : https://prove2.me/theorems/49e520e4-ae5a-41f7-87be-f7bd85984a1a
-- title:
--   Amplification error energy bounded by a residual Gauss energy
-- statement:
--   For a finite set $S$ of ideals, coefficients $c$, a prime $p$ with $(p)$ maximal, `Supported`, avoiding `goodLambda`, of odd residue characteristic, $p\equiv1\bmod$ `goodLambda`$^2$, $n\in\{0,5,6\}$, $T>0$, rows not divisible by $p$, a Schwartz $W$ and $K>0$ with $\operatorname{Re}W(\|\texttt{eisEmbedding}\,z\|^2/K)\ge0$ everywhere and $\ge1$ on rows:
--   $$\sum_{h}\|\texttt{amplificationError}(\dots,T^{-1/2}c,\dots,p,n+1,h)\|^2\le\texttt{localErrorCost}\,p\,n\cdot\frac{\operatorname{Re}\texttt{sourceGaussEnergy}(\texttt{residualColumns}\,S\,p\,(n+1),\,I\mapsto c((p)^{n+1}I),\,\texttt{residualCharacter}\,p\,(n+1),W,K)}{T/N((p))^{n+1}}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentAmplificationErrorEnergy.finite_original_error_energy` in `lean/OAI/NumberTheory/DirichletL/Moments/AmplificationErrorEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

theorem finite_original_error_energy (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2 ∣ p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) (T : ℝ) (hT : 0<T)
    (rows : Finset O) (hrows : ∀ h∈rows,¬p∣h)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑ h∈rows,‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2)≤
      localErrorCost p n *
        ((sourceGaussEnergy (residualColumns S p hp (n+1))
          (fun I => c ((Ideal.span {p})^(n+1)*I))
          (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K).re /
          (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  sorry

end SevenEighths.CenteredMomentAmplificationErrorEnergy

end

end OAI
end
