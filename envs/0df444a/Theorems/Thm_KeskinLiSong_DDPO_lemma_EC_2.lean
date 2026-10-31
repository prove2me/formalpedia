-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_lemma_EC_2
-- name    : KeskinLiSong.DDPO.lemma_EC_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:51:09.62982+00:00
-- url     : https://prove2.me/theorems/58c4ff99-114c-47dc-bf44-0762f465b690
-- title:
--   Lemma EC.2 — moment and sample-cost tails
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. All three clauses share the original constants. Clause (a) is a marginal moment statement, identical for every period of the iid noise sequence. In (b)–(c), the price, estimated beta parameter, optimal stock, reset and sample indices remain data-dependent. The two constants are uniform over all eligible periods and sample lengths. Probabilities and expectations are over noise with the perishability path fixed almost surely. J_tau(ell)=n L(tau)+(n-2m) floor((ell-1)/m)+ell is retained literally, including future innovations when that formula points beyond the sales horizon.
--
--   $$
--   \mathbb E|\varepsilon_t|^k\le k(2\varrho_0\sigma_0^2)^{k/2}\Gamma(k/2)+2^{k+1}k\varpi_0^{-k}\Gamma(k).
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   LEMMA EC.2. (a) For any positive integer k and any period t,
--   E_ε[|ε_t|^k] ≤ k(2ϱ_0σ_0²)^{k/2}Γ(k/2)+2^{k+1}kϖ_0^{−k}Γ(k), (EC.23)
--   where σ_0, ϱ_0, and ϖ_0 are given in the characterization of the distribution of {ε_t}.
--   (b) Given p_t∈P in period t∉𝒳 and s=nL(τ)+1,...,t and s∈𝒳, there exists a positive constant
--   C_5 such that
--   E_ε[exp(ϖ Ω_s^t(p_t,θ_t,ξ̂_t))]
--    ≤ C_5 exp((1/2)ϱ_0σ_0²(|h−c|+b+p_max)²ϖ²) (EC.24)
--   for all ϖ with |ϖ|≤ϖ_0/(|h−c|+b+p_max).
--   (c) Given p_t∈P in period t∉𝒳 and s=nL(τ)+1,...,t with s∈𝒳, there exists a positive constant
--   C_6 such that
--   P_ε{|Σ_{ℓ=1}^u Ω^t_{J_τ(ℓ)}(p_t,θ_t,ξ̂_t)|≥δu}
--    ≤ (2/C_5) exp(−C_6(δ∧δ²)u), (EC.25)
--   for any δ>0 and any u=1,2,...,2m(τ−L(τ)+1), where τ is the cycle to which period t belongs
--   and J_τ(ℓ)=nL(τ)+(n−2m)⌊(ℓ−1)/m⌋+ℓ.
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - reading: tail bounds have random sample sizes and random qualifying cycle ranges → the scalar event probability is bounded almost surely by the random right side on the stated range; reason: literal random-inequality interpretation; neither conditioning nor averaging replaces the displayed bound
--   - generalization: the surrounding model supposes an interior FIA optimum exists → this statement does not require an FIA existence premise; reason: adding that source premise specializes the statement; its estimators, proxies, derivatives or unconstrained-regret contributions do not use the FIA benchmark
--   - encoding: positive-period noise sequence and literal J_tau indexing → independent infinite sequences, signed n-2m, and positivity of selected indices in the conclusion; reason: future noise draws remain available and invalid indexing is not silently truncated
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
--   - reading: P_epsilon and E_epsilon govern the noise sequence while the beta estimate is random → integrate the noise sequence for almost every fixed perishability sequence, recomputing histories and estimates; reason: equation (6) supplies independent primitive sequences; the noise-only subscript does not replace estimated parameters by independent constants
--   - reading: a given price p_t in P → any measurable price selection from the preceding observed history; reason: period prices in Sections 2 and 3 use that information; constants are uniform over those selections within the compact price interval
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Lemma EC.2, printed p. ec8 (PDF p. 40)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

open MeasureTheory ProbabilityTheory

namespace KeskinLiSong.DDPO

theorem lemma_EC_2 (A : Model) (u : Tuning A) :
    (∀ k : ℕ, 1 ≤ k →
      Integrable (fun e : ℝ => |e| ^ k) A.noise.law ∧
      (∫ e, |e| ^ k ∂A.noise.law) ≤
        k * (2 * A.noise.rho * A.noise.sigma ^ 2) ^ ((k : ℝ) / 2) * Real.Gamma ((k : ℝ) / 2) +
        2 ^ (k + 1) * k * A.noise.radius ^ (-(k : ℝ)) * Real.Gamma k) ∧
    (∃ C5 C6 : ℝ, 0 < C5 ∧ 0 < C6 ∧
      ∀ (T : ℕ) (E : Environment A T) (L : Learner .nonparametric),
        Executes .nonparametric A u E L →
        ∀ t ∈ Finset.Icc 1 T, t ∉ experimental u .N T →
        ∀ (p : PriceSelection) (y : Paths T → ℝ), Measurable y →
          (∀ᵐ z ∂primitiveLaw A E, priceAt A E L.policy p z t ∈ A.P ∧
            StockOptimum A A.noise.law (E.theta t) (xiEstimate .nonparametric A E L z t)
              (priceAt A E L.policy p z t) (y z)) →
        ∀ᵐ q ∂perishSequenceLaw A E,
          (∀ s ∈ Finset.Icc 1 T, ∀ a : ℝ,
            |a| ≤ A.noise.radius / (|A.h - A.c| + A.b + A.pmax) →
            Integrable (fun e => Real.exp (a * omegaAt A E L p y (combine e q) t s))
              (noiseSequenceLaw A.noise) ∧
            ∀ᵐ e ∂noiseSequenceLaw A.noise,
              s ∈ samples u .N T (demandPath A E L.policy (combine e q)) t →
              (∫ eps, Real.exp (a * omegaAt A E L p y (combine eps q) t s)
                ∂noiseSequenceLaw A.noise) ≤
                C5 * Real.exp (A.noise.rho * A.noise.sigma ^ 2 *
                  (|A.h - A.c| + A.b + A.pmax) ^ 2 * a ^ 2 / 2)) ∧
          (∀ delta : ℝ, 0 < delta → ∀ count : ℕ, 1 ≤ count →
            let τ := cycleAt u .N T t
            (∀ᵐ e ∂noiseSequenceLaw A.noise,
              let D := demandPath A E L.policy (combine e q)
              count ≤ 2 * m u .N T * (τ - lastReset u .N T D τ + 1) →
              ∀ ell ∈ Finset.Icc 1 count,
                1 ≤ Jindex u .N T D τ ell) ∧
            TailBound (noiseSequenceLaw A.noise)
              (fun e => count ≤ 2 * m u .N T *
                (τ - lastReset u .N T (demandPath A E L.policy (combine e q)) τ + 1))
              (fun e => |∑ ell ∈ Finset.Icc 1 count,
                omegaAt A E L p y (combine e q) t
                  (Jindex u .N T (demandPath A E L.policy (combine e q)) τ ell).toNat|)
              (fun _ => delta * count)
              (fun _ => (2 / C5) * Real.exp (-C6 * min delta (delta ^ 2) * count)))) := by sorry

end KeskinLiSong.DDPO
