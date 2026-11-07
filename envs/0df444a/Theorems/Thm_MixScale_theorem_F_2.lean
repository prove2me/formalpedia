-- Prove2me | Theorems.Thm_MixScale_theorem_F_2
-- name    : MixScale.theorem_F_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:12:41.597273+00:00
-- url     : https://prove2.me/theorems/858a5b4e-2321-4e6e-b3ce-f90dd34f2e03
-- title:
--   Theorem F.2, p.36 — regular-profile separation law for unrestricted weights
-- statement:
--   Let the profile be regular with integers $m,M_{\mathrm{der}}$, radial in the dimensions at hand. Then:
--
--   1. (77) for unrestricted weights, $0<\varepsilon\le\gamma/8$, $0<\delta<1/2$, a global polynomial-time algorithm achieves $D_{\mathrm{par}}\le\varepsilon$ with probability at least $1-\delta$ using $N\le\mathsf P\,\ell_q(\gamma)\gamma^{-E_{q,\alpha}}\varepsilon^{-2}\log(\mathsf P'/\delta)$;
--   2. (78) there is a one-dimensional subclass with $m+1$ components and fixed condition bounds on which every estimator succeeding with probability at least $2/3$ requires $N\ge c\,\ell_q(\gamma)\gamma^{-E_{q,\alpha}}\varepsilon^{-2}$ for $0<\gamma\le c^*$, $0<\varepsilon\le\gamma/8$, even with all centers supplied;
--   3. (79) $E_{q,\alpha}=q+2\alpha$ for $q<1$, $2\alpha+1$ for $q=1$, $2q+2\alpha-1$ for $q>1$;
--   4. for $\alpha\ge1$ the upper bound holds for all $\varepsilon\le1$.
--
--   This is the unrestricted-weight half of Theorem 1.1, including the critical logarithm at $q=1$.
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
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Theorem F.2, p.36 (PDF p.38), (77)–(79)

import Mathlib
import Definitions.Def_MixScale_Regular
import Definitions.Def_MixScale_Laws

namespace MixScale

/-- **Theorem F.2** (Regular-profile separation law for unrestricted weights).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Theorem F.2, p.36 (PDF p.38), (77), (78), (79).

Four clauses, for `S` regular with the integers `m, M_der`:
1. (77), the upper law for `ε ≤ γ/8`;
2. (78), the lower law with `m + 1` components;
3. the exponent table (79);
4. if `α ≥ 1`, the upper law for all `ε ≤ 1`.

**Formalization Note.** `E_{q,α} = Efree q α`. "The critical logarithm is present at `q = 1`" is the
factor `ℓ_q` in clauses 1, 2. -/
theorem theorem_F_2 (S : ProfileSpec) (m Mder : ℕ) (hS : IsRegularProfileAt S m Mder) :
    UpperLaw S .free (fun γ => γ / 8) ∧
    LowerLaw S .free (m + 1) ∧
    (S.q < 1 → Efree S.q S.α = S.q + 2 * S.α) ∧
    (S.q = 1 → Efree S.q S.α = 2 * S.α + 1) ∧
    (1 < S.q → Efree S.q S.α = 2 * S.q + 2 * S.α - 1) ∧
    (1 ≤ S.α → UpperLaw S .free (fun _ => 1)) := by sorry

end MixScale
