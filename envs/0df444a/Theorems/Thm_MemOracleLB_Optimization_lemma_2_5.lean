-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_2_5
-- name    : MemOracleLB.Optimization.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:00.363409+00:00
-- url     : https://prove2.me/theorems/958b7e2f-b367-4218-b1f6-ced53f79692e
-- title:
--   Lemma 2.5 — Gaussian estimates (a)–(d)
-- statement:
--   Let $Z\sim N(0,1)$, $G\sim\gamma_d$, and let $R$ have independent $N(0,1/n)$ entries. All parts of the Gaussian estimate lemma hold:
--
--   1. For $t\ge0$, $\Pr(|Z|\ge t)\le2e^{-t^2/2}$.
--   2. For $h>0$, $\Pr(\|G\|^2>d(1+h))\le e^{-d(h-\log(1+h))/2}$.
--   3. For any $r$-dimensional subspace $L$, $\|P_LG\|^2$ has law $\chi_r^2$. The same conditional law holds for an independent random $L$. In particular,
--      $$\Pr(\chi_2^2\le u)=1-e^{-u/2}\quad(u\ge0).$$
--   4. For $n>0$ and $x>0$,
--      $$\Pr(\|R^{-1}\|_{\rm op}\ge x)\le n/x.$$
--
--   The conditional clause is a joint product-law identity on every measurable event of the random-subspace parameter, not merely a marginal identity. Chi-square rank zero is a point mass at zero. The exact inverse-norm constant is retained.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - generalization: the large ambient dimension convention → all Gaussian vector dimensions d and every positive matrix size n; reason: the four estimates hold on this larger domain and include all source instances
--   - encoding: a random subspace independent of G and its conditional chi-square law → an arbitrary parameter probability space independent of G, almost-sure rank r, and a measurable squared projection norm with the joint product-law identity; reason: this is precisely the conditional-law assertion without selecting a version of conditional probabilities
--   - encoding: an inverse of an almost surely nonsingular Gaussian matrix → the total matrix inverse, whose singular branch is zero; reason: the singular set has probability zero and cannot contribute to the positive-threshold event
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 2.5, PDF p. 9 (printed p. 8), continues on PDF p. 10, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_OracleModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
universe u25

namespace MemOracleLB.Optimization

/-- Lemma 2.5(a)–(d), PDF pp.9–10 (printed pp.8–9).
Part (c)'s product-law identity states the conditional law, not just its average. -/
theorem lemma_2_5 :
    (∀ t : ℝ, 0 ≤ t → (gaussianReal 0 1) {z | t ≤ |z|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2))) ∧
    (∀ (d : ℕ) (h : ℝ), 0 < h →
      stdGaussian (E d) {x | (d : ℝ) * (1 + h) < ‖x‖ ^ 2} ≤
        ENNReal.ofReal (Real.exp (-(d : ℝ) * (h - Real.log (1 + h)) / 2))) ∧
    (∀ (d : ℕ) (L : Submodule ℝ (E d)),
      (stdGaussian (E d)).map (fun x => ‖L.orthogonalProjectionOnto x‖ ^ 2) =
        chiSquare (Module.finrank ℝ L)) ∧
    (∀ {Ω : Type u25} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
      (d r : ℕ) (L : Ω → Submodule ℝ (E d)),
      (∀ᵐ ω ∂ρ, Module.finrank ℝ (L ω) = r) →
      Measurable (fun p : Ω × E d => ‖(L p.1).orthogonalProjectionOnto p.2‖ ^ 2) →
      ∀ (B : Set Ω), MeasurableSet B → ∀ (S : Set ℝ), MeasurableSet S →
        (ρ.prod (stdGaussian (E d)))
          {p | p.1 ∈ B ∧ ‖(L p.1).orthogonalProjectionOnto p.2‖ ^ 2 ∈ S} =
          ρ B * chiSquare r S) ∧
    (∀ u : ℝ, 0 ≤ u → chiSquare 2 (Set.Iic u) =
      ENNReal.ofReal (1 - Real.exp (-u / 2))) ∧
    (∀ (n : ℕ), 0 < n → ∀ x : ℝ, 0 < x →
      matrixLaw n {R | x ≤ matrixOpNorm (rowMatrix R)⁻¹} ≤ ENNReal.ofReal (n / x)) := by sorry

end MemOracleLB.Optimization
