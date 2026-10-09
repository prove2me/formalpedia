-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_long_bin_normalized_energy
-- name    : OAI.SevenEighths.InverseMoment.actual_long_bin_normalized_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:46:44.149898+00:00
-- url     : https://prove2.me/theorems/2154bf18-914b-4f51-83a2-d63877935f5a
-- title:
--   Normalized energy of a long reopened cube bin
-- statement:
--   Let $S$ be a finite set of prime ideals of $\mathcal O$ (Eisenstein integers) containing `fixedBadPrimes`, $D\in\mathbb N$, $Q$ a finite set of finitely supported exponent vectors on `primePool (outsideSquarefreeIdeals S D)`, `labels` a finite set of ideals, $\Psi$ multiplicative, $m\in\mathcal O$, $W$ smooth with support in $[a,b]$ ($0<a$, $0\le b$), $V$ Schwartz with $V(u)=1$ for $|u|\le$ `columnWindowRadius a b`, reals $Z>0$, $r$, `cubeLength`, `Vheight`, $H_0$, $K>0$, $E\ge0$ with $b\,Z^{r+3\,\mathrm{cubeLength}}\le D$, $d\in\mathbb N$, every cube ideal of $v\in Q$ of absolute norm in $[Z^{\mathrm{cubeLength}},e\,Z^{\mathrm{cubeLength}}]$, and slot data (`slots`, `lists`, `weights`). If for every real $\xi$ the `rowFamilyEnergy` (with $K$) of the separated reopened rows (built from `varyingReopenedRow`, `separatedCubeCoefficient`, `primeMark` and `frequencyTwist V ξ`), times $Z^{-r-2\,\mathrm{cubeLength}-\mathrm{Vheight}}$, is at most $E(1+|\xi|)^{2d}$, then $Z^{-\mathrm{Vheight}}$ times the `rowFamilyEnergy` of the `markedReopenedCubeBin` rows is at most
--   $$E\Big(\int_{\mathbb R}\|\texttt{reopeningCoefficient}\,W\,a\,b\,(\xi)\|(1+|\xi|)^d\,d\xi\Big)^2.$$
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_long_bin_normalized_energy` in `lean/OAI/NumberTheory/DirichletL/Descent/CanonicalLongIntegral.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B009

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem actual_long_bin_normalized_energy
    {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0≤b) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Z r cubeLength Vheight H₀ K E : ℝ) (d : ℕ)
    (hZ : 0 < Z) (hD : b*(Z^(r+3*cubeLength))≤D) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, (Z^cubeLength) ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*(Z^cubeLength))
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, Z^(-r-2*cubeLength-Vheight)*rowFamilyEnergy labels (fun I z =>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n (Z^cubeLength) ξ) Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) (Z^r) T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    Z^(-Vheight)*rowFamilyEnergy labels (fun I z =>
      markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W (Z^(r+3*cubeLength)) H₀ slots lists weights) K ≤
      E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
