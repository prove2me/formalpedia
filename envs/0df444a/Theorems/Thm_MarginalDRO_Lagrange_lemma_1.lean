-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_lemma_1
-- name    : MarginalDRO.Lagrange.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:40.522391+00:00
-- url     : https://prove2.me/theorems/5919f510-f7b3-4845-9960-fe466bc36c3a
-- title:
--   Lemma 1 (Monotone Coupling Lemma), pp. 13–14 — for h(x,y)=xy, the monotone coupling attains sup E[xy] = ∫₀¹ F⁻¹_µ(t)F⁻¹_ν(t)dt
-- statement:
--   Let $\mu$ and $\nu$ be probability measures on $\mathbb R$, with $\mu$ of finite mean and $\nu$ concentrated on a finite set $A$. Write $F_\mu^{-1}(t) = \inf\{x : F_\mu(x) > t\}$ for the quantile function. Let $\gamma_{\mathrm{mono}}$ be the **monotone coupling**, the law of $(F_\mu^{-1}(U), F_\nu^{-1}(U))$ for $U$ uniform on $(0,1)$. Then:
--
--   1. $\gamma_{\mathrm{mono}}$ is a coupling of $\mu$ and $\nu$;
--   2. $E_{\gamma_{\mathrm{mono}}}[xy] = \int_0^1 F_\mu^{-1}(t)\,F_\nu^{-1}(t)\,dt$;
--   3. this value is the largest expectation over all couplings:
--   $$\max_{\gamma \in \Gamma(\mu,\nu)} E_{(x,y)\sim\gamma}[x\,y] = \int_0^1 F_\mu^{-1}(t)\,F_\nu^{-1}(t)\,dt .$$
--
--   This is the supermodular case $h(x,y) = xy$ of the monotone coupling lemma; applied coordinate by coordinate with $\nu = \Pi_i\nu$ it turns the coupling form of the primal problem into the quantile form (8) of Theorem 3.
--
--   **Formalization Note** The paper states the lemma for a general right-continuous supermodular $h$ and also gives the matching infimum (antitone coupling); only the case $h(x,y)=xy$ and the supremum, which the proof of Theorem 3 uses, are stated here. The paper prints no moment condition; the hypotheses "$\mu$ has finite mean, $\nu$ finitely supported" make $E[xy]$ finite for every coupling. The quantile's default value at $t \in \{0,1\}$ concerns a null set.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), pp. 13–14, Lemma 1 (Theorem 3.1.2 in Rachev and Rüschendorf (1998)), sup line; used on p. ec7 (PDF 55)

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- Lemma 1 (Monotone Coupling Lemma), pp. 13–14, sup half, for `h(x, y) = x y` and a
finitely supported second law. -/
theorem lemma_1 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (A : Finset ℝ) (hA : ν ((A : Set ℝ)ᶜ) = 0) :
    ((volume.restrict (Set.Ioo (0 : ℝ) 1)).map (fun t => (quantile μ t, quantile ν t)))
        ∈ couplings μ ν ∧
      ∫ p, p.1 * p.2 ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).map
          (fun t => (quantile μ t, quantile ν t))) =
        ∫ t in (0 : ℝ)..1, quantile μ t * quantile ν t ∧
      IsGreatest {s | ∃ γ ∈ couplings μ ν, s = ∫ p, p.1 * p.2 ∂γ}
        (∫ t in (0 : ℝ)..1, quantile μ t * quantile ν t) := by sorry
end MarginalDRO.Lagrange
