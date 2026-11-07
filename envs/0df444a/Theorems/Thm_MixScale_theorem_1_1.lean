-- Prove2me | Theorems.Thm_MixScale_theorem_1_1
-- name    : MixScale.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:12:50.208536+00:00
-- url     : https://prove2.me/theorems/af87fc9f-d2d4-4651-861d-5adf299629cd
-- title:
--   Theorem 1.1, p.3 — sharp rate $\ell_q(\gamma)\gamma^{-E_W}\varepsilon^{-2}$ for a fixed regular profile, both weight classes
-- statement:
--   Fix a profile satisfying Definition F.1, with $\tau=\min(q,1)$, $\ell_q(\gamma)=\log(e/\gamma)$ for $q=1$ and $1$ otherwise, $E_{\mathrm{free}}=2(q+\alpha)-\tau$ and $E_{\mathrm{eq}}=2q-\tau$. Let $W$ be either weight class.
--
--   1. There is a global polynomial-time algorithm under (2) (with $w_j=1/k$ for equal weights) that, for $0<\varepsilon\le\gamma/8$ and $0<\delta<1/2$, uses
--
--   $$N\le\mathsf P\,\ell_q(\gamma)\gamma^{-E_W}\varepsilon^{-2}\log(\mathsf P'/\delta)$$
--
--   samples and returns $\hat\Theta$ with $D_{\mathrm{par}}(\hat\Theta,\Theta)\le\varepsilon$ with probability at least $1-\delta$. In the equal-weight class, all output weights equal $1/k$. The polynomials $\mathsf P,\mathsf P'$ in $(d,k,B,\kappa,w_\star^{-1})$ have degrees independent of $d,k$ and contain no $\gamma^{-1},\varepsilon^{-1}$.
--
--   2. Conversely, there is a fixed-size one-dimensional subclass with fixed valid condition bounds on which every estimator succeeding with probability at least $2/3$ requires
--
--   $$N\ge c\,\ell_q(\gamma)\gamma^{-E_W}\varepsilon^{-2},\qquad0<\gamma\le c^*,\ 0<\varepsilon\le\gamma/8,$$
--
--   even with the centers supplied, and with the multiset of scales also supplied under equal weights. The constants and the component count may depend on the profile and the weight class.
--
--   The separation exponents differ by exactly $2\alpha$: recovering scale from the first Fourier correction, rather than from the leading amplitude, costs an extra factor $\gamma^{-2\alpha}$.
--
--   Differences from the source:
--   - reading: a global polynomial-time algorithm in "the real-arithmetic model" with "elementary function evaluation" and effective profile access (p.3, p.48), no instruction list → a MixScale.Machine program: real RAM core with rational literals, √, exp, log, cos, sin, fair coins, standard Gaussian draws, sample (cost d) and an adversarial profile oracle (cost ⌈evalC(1+1/η)^evalD⌉), with profile constants as inputs; reason: the paper names the model only; Gaussian draws are used in (43); the oracle is item 3 of Definition A.1
--   - reading: polynomial time → on every run, work ≤ C_T(C γ⁻¹ ε⁻¹ log(2/δ))^{D_T}; reason: the count on p.48 is O(dNQ) with N, Q ∝ log(1/δ), so log(1/δ) is the honest variable; time polynomial in 1/δ would be weaker
--   - reading: uses N ≤ … samples → the sample bound holds on every run and every admissible oracle, not in expectation; reason: "All branches have a predetermined polynomial operation budget" (p.48)
--   - reading: returns Θ̂; "The output must be a valid mixture" (p.2); in the equal-weight class, all mixing weights equal 1/k → on every run the output is legal, and has all weights 1/k for W = eq; reason: task definition on p.2, Algorithm 1 "A legal k-component tuple", and the fallback on p.48 and p.50
--   - encoding: positive fixed-degree polynomials P, P′ in C = (d, k, B, κ, w★⁻¹) → C₀(dkBκ/w★)^D and C₀′(dkBκ/w★)^{D′}, chosen after the profile and weight class, before all other parameters; reason: every variable of C is ≥ 1 on the inputs, so each form bounds the other
--   - encoding: P_Θ = Σ w_j P_{μ_j,Σ_j} with characteristic function (1) → the guarantee holds for every family of probability measures with characteristic function (1), mixed with weights w_j; reason: the family is unique by uniqueness of characteristic functions and exists (checked in the sanity file)
--   - encoding: with probability at least 1 − δ → ∃ measurable E ⊆ {success} with 1 − δ ≤ P(E); reason: avoids outer measure; equal to the ordinary probability when the success set is measurable
--   - encoding: d, k given (implicitly positive) → 0 < d and 0 < k; reason: dimension and component count are positive throughout; only degenerate inputs are excluded
--   - encoding: Definition F.1 (L¹ derivative, ∂_s^j ĥ_v, continuous representatives, a.e. meaning at infinite-density points) → ∃ m, M_der; L¹ difference-quotient limit written with lower integrals; derivatives within {|s| ≥ 1}, assumed C^{M_der} there; h_v^{(m)} of an ∃-quantified representative C^m off zero; density f real valued; reason: these are the printed conditions; f(0) does not matter and no extra smoothness is added
--   - encoding: every estimator (possibly randomized) → any function of the samples and an independent seed on any probability space, with success via ∃ measurable E ⊆ {success}; reason: a measurable estimator has its ordinary success probability; no measurability is assumed
--   - encoding: c∗ positive → c∗ ≤ 1 in addition; reason: the model has γ ≤ 1 (p.2), so c∗ can be replaced by min(c∗, 1)
--   - generalization: χ a radial characteristic function "in every dimension under consideration" → the hypothesis IsRadialCF χ d only for the dimension d at hand, with the program chosen before d; reason: a profile radial in every dimension satisfies it for each d, so this specializes to the paper
--   - generalization: a fixed-size one-dimensional subclass on which every estimator succeeding with probability at least 2/3 requires N ≥ …, even with supplied centers (and scale multiset for eq) → for each γ, ε a two-point pair in the subclass with equal center lists (and equal scale multisets for eq), and any randomized estimator succeeding on both; reason: an estimator succeeding on any subclass containing the pair succeeds on both; supplied data are constant on the pair, so the estimator depending on them is one estimator
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Theorem 1.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_MixScale_Regular
import Definitions.Def_MixScale_Laws

namespace MixScale

/-- **Theorem 1.1** (Sharp rate for a fixed regular profile).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Theorem 1.1, p.3 (PDF p.5).

For a profile satisfying Definition F.1 and either weight class `W`:
* (upper) a program, polynomial constants and degrees chosen after `S, W` and before every other
  parameter, such that on every run the program halts within a polynomial work budget, uses at most
  `P ℓ_q(γ) γ^{−E_W} ε^{−2} log(P′/δ)` samples, outputs a legal tuple (equal weights for `eq`), and
  has `D_par ≤ ε` with probability at least `1 − δ`, for `0 < ε ≤ γ/8`, `0 < δ < 1/2`;
* (lower) a fixed-size one-dimensional two-point family with fixed condition bounds and identical
  centers (and scale multisets for `eq`) on which every randomized estimator succeeding with
  probability at least `2/3` under both alternatives uses `N ≥ c ℓ_q(γ) γ^{−E_W} ε^{−2}` samples, for
  `0 < γ ≤ c∗`, `0 < ε ≤ γ/8`.

**Formalization Note.** See `UpperLaw`, `LowerLaw`, `MixScale.Machine`. -/
theorem theorem_1_1 (S : ProfileSpec) (hS : ∃ m Mder : ℕ, IsRegularProfileAt S m Mder)
    (W : WeightClass) :
    UpperLaw S W (fun γ => γ / 8) ∧ ∃ k₀ : ℕ, 0 < k₀ ∧ LowerLaw S W k₀ := by sorry

end MixScale
