-- Prove2me | Theorems.Thm_GMMIsoSample_Main_lemma_12
-- name    : GMMIsoSample.Main.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:24.588082+00:00
-- url     : https://prove2.me/theorems/4ecf30b5-91fb-4299-9456-a0ff8790e10f
-- title:
--   Lemma 12 — for k = 2, ConstructHypothesisDistribution2 on N ≥ N_CMS,2 truly clustered points is ε-accurate up to isometry w.p. ≥ 99/100
-- statement:
--   Fix $w_{\min}>0$. There is a constant $C_{w_{\min}}>0$, depending only on $w_{\min}$, such that for every $0<\varepsilon<1/10$ and all sufficiently large $d$: for every two-component target $D=w_1N(\mu_1,\sigma_1^2I_d)+w_2N(\mu_2,\sigma_2^2I_d)$ with $w_1,w_2\ge w_{\min}$ and $\Gamma(D)\ge\Gamma_{\min}>0$, and every
--   $$N\ge N_{CMS,2}=C_{w_{\min}}\Big(\frac1{\varepsilon^2}+\frac{\sqrt d}{\varepsilon\Gamma_{\min}}\Big)\log\frac{100}\delta\qquad(\delta=1/100),$$
--   ConstructHypothesisDistribution2 run on the true clustering $S'_1\sqcup S'_2$ of $N$ i.i.d. points from $D$ outputs a two-component spherical Gaussian mixture $\hat D$ with $\inf_{\tau\in\mathrm{Iso}(\mathbb R^d)}d_{TV}(\hat D,\tau(D))\le\varepsilon$, with probability at least $99/100$.
--
--   This is the $k=2$ reconstruction step of the upper bound; its $\sqrt d/(\varepsilon\Gamma_{\min})$ term is the source of the $\sqrt d/\Gamma_{\min}$ rate in Theorem 2(a).
--
--   Differences from the source:
--
--   - reading: 'for sufficiently large d, there is a constant C_wmin > 0, depending only on wmin' → ∃ C before ε and d; ∃ d₀ depending on wmin and ε, uniform in Γmin, D and N; reason: the subscript says C depends only on wmin; d₀ cannot depend on D, which lives in ℝ^d
--   - encoding: Γmin a promised lower bound on Γ(D), positive throughout the paper (N_CMS,2 in (15) divides by Γmin) → hypothesis 0 < Γmin; reason: excludes only the undefined or meaningless case Γmin ≤ 0
--   - encoding: 'outputs a two-component spherical Gaussian mixture D̂ such that, with probability ≥ 99/100, inf_τ dTV(D̂, τ(D)) ≤ ε' → with probability ≥ 99/100 the algorithm does not fail, D̂ is a valid mixture (positive radii, weights summing to 1) and inf_τ dTV(D̂, τ(D)) ≤ ε; reason: a failure or a degenerate radius is not a spherical Gaussian mixture
--   - encoding: target D = Mix(μ̄, σ̄, w̄), components indexed by [k] → a parameter tuple p : Fin k → ℝ × ℝ × ℝ^d (0-based) with mix p = Σ w_i N(μ_i, σ_i² I_d); reason: the paper itself parametrizes targets by these tuples; Γ(D) ≥ Γ is the pairwise condition over i ≠ j
--   - encoding: i.i.d. sample points from D together with their (unobserved) component labels → an i.i.d. sample from labeledMix p, the joint law of (label, point); reason: the points' marginal is D; the labels define the true clustering the statement refers to
--   - encoding: uniformly random subsets / pairings / partitions chosen by the algorithm → read off one uniformly random permutation of the indices (average over all permutations); reason: consecutive runs of a uniformly permuted list are uniformly random disjoint subsets and a uniformly random pairing / partition
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 17, Lemma 12 (Figure 3, p. 21)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_Clustering
import Definitions.Def_GMMIsoSample_Main_Hypothesis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Lemma 12 (p. 17): there is `C_wmin > 0` depending only on `wmin` such that for every
`0 < ε < 1/10` and all sufficiently large `d`: for every two-component target
`D = w₁N(μ₁, σ₁² I_d) + w₂N(μ₂, σ₂² I_d)` with `w₁, w₂ ≥ wmin` and `Γ(D) ≥ Γmin`, and every
`N ≥ N_CMS,2 = C_wmin (1/ε² + √d/(εΓmin)) log(100/δ)` (`δ = 1/100`), run on the true clustering
`S'₁ ⊔ S'₂` of `N` i.i.d. points from `D`, ConstructHypothesisDistribution2 outputs a
two-component spherical mixture `D̂` with `inf_{τ ∈ Iso(ℝ^d)} d_TV(D̂, τ(D)) ≤ ε`, with
probability at least `99/100` (over the sample and the algorithm's uniform random permutation). -/
theorem lemma_12 :
    ∀ wmin : ℝ, 0 < wmin → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γmin : ℝ, 0 < Γmin →
        ∀ p : Params d 2, IsTarget 2 wmin Γmin p → ∀ N : ℕ, nCMS2 C ε d Γmin ≤ N →
          avgPerm N (fun π => iidLaw (labeledMix p) N
            {x | ¬ HypSucceeds ε (mix p) (chd2 x π)}) ≤ 1 / 100 := by sorry

end GMMIsoSample.Main
