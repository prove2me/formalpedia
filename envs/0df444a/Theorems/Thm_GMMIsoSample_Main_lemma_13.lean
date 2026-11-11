-- Prove2me | Theorems.Thm_GMMIsoSample_Main_lemma_13
-- name    : GMMIsoSample.Main.lemma_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:42.211955+00:00
-- url     : https://prove2.me/theorems/ea614f4f-53a1-4d4c-b239-9b6f33d9c1e7
-- title:
--   Lemma 13 — for k ≥ 3, ConstructHypothesisDistributionk on N ≥ N_CMS,kmax truly clustered points is ε-accurate up to isometry w.p. ≥ 99/100
-- statement:
--   Fix $k_{\max}>2$ and $0<w_{\min}\le1/3$. There is a constant $C_{k_{\max},w_{\min}}>0$ such that for every $0<\varepsilon<1/10$ and all sufficiently large $d$: for every $k$-component target $D=\sum_{i=1}^kw_iN(\mu_i,\sigma_i^2I_d)$ with $3\le k\le k_{\max}$, $w_i\ge w_{\min}$ and $\Gamma(D)\ge\Gamma_{\min}>0$, and every
--   $$N\ge N_{CMS,k_{\max}}=C_{k_{\max},w_{\min}}\frac{\sqrt d}{\varepsilon^2}\log\frac{k_{\max}}\delta\qquad(\delta=1/100),$$
--   ConstructHypothesisDistributionk run on the true clustering of $N$ i.i.d. points from $D$ outputs a $k$-component spherical Gaussian mixture $\hat D$ with $\inf_{\tau}d_{TV}(\hat D,\tau(D))\le\varepsilon$, with probability at least $99/100$, whatever its free choices.
--
--   This is the $k\ge3$ reconstruction step; the $\sqrt d/\varepsilon^2$ budget is the source of the $\sqrt d$ rate in Theorem 2(b).
--
--   Differences from the source:
--
--   - reading: 'for sufficiently large d, there is a constant C_{kmax,wmin} > 0' → ∃ C before ε and d; ∃ d₀ depending on kmax, wmin, ε, uniform in Γmin, D and N; reason: the subscript says C depends only on kmax and wmin
--   - encoding: Γmin a promised lower bound on Γ(D), positive throughout the paper (N_CMS,2 in (15) divides by Γmin) → hypothesis 0 < Γmin; reason: excludes only the undefined or meaningless case Γmin ≤ 0
--   - reading: free choices of Figure 4 (ties for the anchor a, the diagonalization defining S₊, the factor X̂) → the success event holds for every admissible choice; failure if no admissible choice exists; reason: the paper leaves these choices free ('breaking ties arbitrarily', 'Choose X̂')
--   - encoding: 'outputs a k-component spherical Gaussian mixture D̂ such that, with probability ≥ 99/100, …' → with probability ≥ 99/100 the algorithm does not fail, D̂ is valid and inf_τ dTV(D̂, τ(D)) ≤ ε; reason: a failure or a degenerate radius is not a spherical Gaussian mixture
--   - encoding: target D = Mix(μ̄, σ̄, w̄), components indexed by [k] → a parameter tuple p : Fin k → ℝ × ℝ × ℝ^d (0-based) with mix p = Σ w_i N(μ_i, σ_i² I_d); reason: the paper itself parametrizes targets by these tuples; Γ(D) ≥ Γ is the pairwise condition over i ≠ j
--   - encoding: i.i.d. sample points from D together with their (unobserved) component labels → an i.i.d. sample from labeledMix p, the joint law of (label, point); reason: the points' marginal is D; the labels define the true clustering the statement refers to
--   - encoding: uniformly random subsets / pairings / partitions chosen by the algorithm → read off one uniformly random permutation of the indices (average over all permutations); reason: consecutive runs of a uniformly permuted list are uniformly random disjoint subsets and a uniformly random pairing / partition
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 17, Lemma 13 (Figure 4, p. 27)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_Clustering
import Definitions.Def_GMMIsoSample_Main_Hypothesis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Lemma 13 (p. 17): for `kmax > 2` and `0 < wmin ≤ 1/3` there is `C_{kmax,wmin} > 0` such that
for every `0 < ε < 1/10` and all sufficiently large `d`: for every `k`-component target `D` with
`3 ≤ k ≤ kmax`, weights `≥ wmin` and `Γ(D) ≥ Γmin`, and every
`N ≥ N_CMS,kmax = C_{kmax,wmin} (√d/ε²) log(kmax/δ)` (`δ = 1/100`), run on the true clustering of
`N` i.i.d. points from `D`, ConstructHypothesisDistributionk outputs a `k`-component spherical
mixture `D̂` with `inf_τ d_TV(D̂, τ(D)) ≤ ε` with probability at least `99/100`, whatever its free
choices (anchor tie-break, diagonalization, factor `X̂`). -/
theorem lemma_13 :
    ∀ kmax : ℕ, 2 < kmax → ∀ wmin : ℝ, 0 < wmin → wmin ≤ 1 / 3 →
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γmin : ℝ, 0 < Γmin →
        ∀ (k : ℕ) (p : Params d k), 3 ≤ k → IsTarget kmax wmin Γmin p →
        ∀ N : ℕ, nCMSk C ε d kmax ≤ N →
          avgPerm N (fun π => iidLaw (labeledMix p) N
            {x | ∃ o ∈ chdkOutputs x π, ¬ HypSucceeds ε (mix p) o}) ≤ 1 / 100 := by sorry

end GMMIsoSample.Main
