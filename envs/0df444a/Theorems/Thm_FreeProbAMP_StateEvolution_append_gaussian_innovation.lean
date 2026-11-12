-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_append_gaussian_innovation
-- name    : FreeProbAMP.StateEvolution.append_gaussian_innovation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:59.260107+00:00
-- url     : https://prove2.me/theorems/806810dd-ca0d-4659-b245-388f01f9750e
-- title:
--   Lemma 6.5 — append a Gaussian innovation and small error
-- statement:
--   Let $X_i^d\in\mathbb R^q$ be measurable for $\mathcal H_d$, and suppose it converges empirically to an all-moment $X$. Let $\mathcal H_d$-measurable $b_d\in\mathbb R^q$, $\sigma_d\ge0$ converge in probability to deterministic $b,\sigma\ge0$. Let $Z_1^d,\ldots,Z_{n(d)}^d$ be independent standard normals independent of $\mathcal H_d$. Suppose the error vector satisfies
--
--   $$\|r^d\|_n\xrightarrow{\mathbb P}0,\qquad
--   \frac1{n(d)}\sum_i|r_i^d|^{2p}=O_{\mathbb P}(1)\quad\text{for every integer }p\ge1.$$
--
--   For $Y_i^d=b_d^\top X_i^d+\sigma_d Z_i^d+r_i^d$,
--
--   $$(X_i^d,Y_i^d)_{i\le n(d)}\xrightarrow{\rm emp}(X,b^\top X+\sigma Z),$$
--
--   where $Z$ is a standard normal independent of $X$. This applies to every such independent limiting realization. Zero $\sigma$ is allowed, and no independence of $r^d$ from any other variable is assumed. This is the innovation-closure statement for the vector update.
--
--   Differences from the source:
--   - encoding: random vectors and matrix observations → explicit measurability of random data and almost-everywhere symmetry; reason: the standing random-variable convention is made explicit; no distribution is excluded
--   - encoding: sample sizes n(d) with n(d) → ∞ → n(d) ≥ 1 for every d; reason: nondegeneracy only; at n = 0 the source's 1/n and n^{-1/2} normalizations are undefined, and n(d) → ∞ leaves only finitely many such d, which no limit statement sees
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), pp. 30–31, Lemma 6.5, including (6.3)

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Lemma 6.5, submission pp.30–31, including zero variance and dependent errors. -/
theorem append_gaussian_innovation
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ → ℕ) (q : ℕ) (hn : ∀ d, 0 < n d)
    (H : ℕ → MeasurableSpace Ω) (hH : ∀ d, H d ≤ ‹MeasurableSpace Ω›)
    (X : (d : ℕ) → Ω → Fin (n d) → Fin q → ℝ) (Y : E → Fin q → ℝ)
    (hx : ∀ d, Measurable[H d] (X d)) (he : Empirical μ ν n X Y)
    (b : ℕ → Ω → Fin q → ℝ) (σ : ℕ → Ω → ℝ) (b₀ : Fin q → ℝ) (σ₀ : ℝ)
    (hb : ∀ d, Measurable[H d] (b d)) (hs : ∀ d, Measurable[H d] (σ d))
    (hspos : ∀ d ω, 0 ≤ σ d ω) (hs0 : 0 ≤ σ₀)
    (hbl : InProb μ (fun d ω => euclid (b d ω-b₀)) 0) (hsl : InProb μ σ σ₀)
    (Z : (d : ℕ) → Ω → Fin (n d) → ℝ)
    (hz : ∀ d, Measurable (Z d) ∧
      μ.map (Z d) = Measure.pi (fun _ : Fin (n d) => gaussianReal 0 1) ∧
      Indep (sigma (Z d)) (H d) μ)
    (r : (d : ℕ) → Ω → Fin (n d) → ℝ) (hrm : ∀ d, Measurable (r d))
    (hr0 : InProb μ (fun d ω => vecNorm (r d ω)) 0)
    (hrp : ∀ p : ℕ, 1 ≤ p → Tight μ (fun d ω => avg (n d) (fun i => |r d ω i|^(2*p))))
    (Z₀ : E → ℝ) (hz0 : Measurable Z₀) (hl0 : ν.map Z₀ = gaussianReal 0 1)
    (hi0 : IndepFun Y Z₀ ν) :
    Empirical μ ν n
      (fun d ω i => append (X d ω i) ((∑ j, b d ω j * X d ω i j) + σ d ω*Z d ω i + r d ω i))
      (fun ξ => append (Y ξ) ((∑ j, b₀ j * Y ξ j) + σ₀*Z₀ ξ)) := by sorry

end FreeProbAMP.StateEvolution
