-- Prove2me | Theorems.Thm_MarkovCLTRate_eq_9_10_weighted_ergodicity_poisson
-- name    : MarkovCLTRate.eq_9_10_weighted_ergodicity_poisson
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:08.989982+00:00
-- url     : https://prove2.me/theorems/02d85268-4e1c-45b6-bc3e-d61af951388d
-- title:
--   (9)–(10): weighted geometric ergodicity and the reward Poisson solution
-- statement:
--   Assume the standing assumptions of Theorem 3. Then:
--
--   1. if $L\ge0$, for every $s\in(0,1]$ and $x$, $P\mathcal V^s(x)\le(P\mathcal V(x))^s\le\lambda^s\mathcal V(x)^s+L^s$;
--   2. for every $s\in(0,1]$ there are $C_s<\infty$ and $\rho_s\in(0,1)$ with
--   $$
--   |P^jf(x)-\pi f|\le C_s\rho_s^j\|f\|_{\mathcal V^s}\big(1+\mathcal V(x)^s\big)\qquad(9)
--   $$
--   for all $j\ge0$, all $x$ and every measurable $f$ with $\|f\|_{\mathcal V^s}=\sup_x|f(x)|/(1+\mathcal V(x)^s)<\infty$;
--   3. for $2<p\le4$ and a measurable, $\pi$-integrable reward $r$ with $\|g(x)\|^p\le C_r\mathcal V(x)$, the Poisson equation $V_r-PV_r=g$ has a solution with
--   $$
--   \|V_r(x)\|\le C\big(1+\mathcal V(x)^{1/p}\big).\qquad(10)
--   $$
--
--   These are the weighted ergodic and Poisson-equation estimates of Meyn and Tweedie on which the rest of the proof rests.
--
--   **Formalization Note** In item 1, $P\mathcal V^s$ and $P\mathcal V$ are lower Lebesgue integrals. In item 2, $\|f\|_{\mathcal V^s}$ is a real supremum, and assuming the ratio bounded above makes it the true one.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
--   - encoding: λ^s𝒱(x)^s + L^s with L < ∞ → the Jensen clause assumes 0 ≤ L; reason: L^s is a real power of L and is undefined for L < 0; the condition only excludes that undefined case
--   - encoding: ‖f‖_{𝒱^s} := sup_x |f(x)|/(1 + 𝒱(x)^s) < ∞ → BddAbove of the ratio, and ⨆ x of the ratio; reason: a real supremum is the true one exactly when the set is bounded above
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.18, Jensen step, (9), (10)

import Mathlib
import Definitions.Def_MarkovIterKernel
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **The Jensen step, (9) and (10)**, arXiv:2401.15719v5, proof of Theorem 3, p.18. Under the
assumptions of Theorem 3:
1. for every `s ∈ (0, 1]`, `P𝒱^s(x) ≤ (P𝒱(x))^s ≤ λ^s 𝒱(x)^s + L^s`;
2. (9) for every `s ∈ (0, 1]` there are `C_s < ∞` and `ρ_s ∈ (0, 1)` with
   `|P^j f(x) − πf| ≤ C_s ρ_s^j ‖f‖_{𝒱^s} (1 + 𝒱(x)^s)` for all `j ≥ 0`, `x ∈ S` and all measurable
   `f : S → ℝ` with `‖f‖_{𝒱^s} = sup_x |f(x)| / (1 + 𝒱(x)^s) < ∞`;
3. (10) for `2 < p ≤ 4`, `r` measurable and `π`-integrable with `‖g‖^p ≤ C_r 𝒱`, the Poisson
   equation `V_r − PV_r = g` has a solution with `‖V_r(x)‖ ≤ C(1 + 𝒱(x)^{1/p})`.

**Formalization Note.** In item 1, `P𝒱^s(x)` and `P𝒱(x)` are lower Lebesgue integrals; the last
inequality needs `L ≥ 0` for `L^s` to be a real power of a nonnegative number, so item 1 assumes
it. In item 2, `‖f‖_{𝒱^s}` is a real supremum, and the hypothesis that the ratio is bounded above
makes it the true supremum. Item 3 is (10) with `a = 1/p`, for the parameter `p = 2 + β` of item 1
of Theorem 3 and `p = 4` of item 2 (p.22). -/
theorem eq_9_10_weighted_ergodicity_poisson {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (hchain : GeoDriftChain P π η lyap lam L) :
    (0 ≤ L → ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ x : S,
        (∫⁻ y, ENNReal.ofReal (lyap y ^ s) ∂(P x))
            ≤ (∫⁻ y, ENNReal.ofReal (lyap y) ∂(P x)) ^ s ∧
        (∫⁻ y, ENNReal.ofReal (lyap y) ∂(P x)) ^ s
            ≤ ENNReal.ofReal (lam ^ s * lyap x ^ s + L ^ s)) ∧
    (∀ s : ℝ, 0 < s → s ≤ 1 → ∃ Cs ρs : ℝ, 0 < ρs ∧ ρs < 1 ∧
        ∀ f : S → ℝ, Measurable f →
          BddAbove (Set.range fun x => |f x| / (1 + lyap x ^ s)) →
          ∀ (j : ℕ) (x : S),
            |∫ y, f y ∂(MarkovChainCLT.iterKernel P j x) - ∫ y, f y ∂π|
              ≤ Cs * ρs ^ j * (⨆ z, |f z| / (1 + lyap z ^ s)) * (1 + lyap x ^ s)) ∧
    (∀ (r : S → Vec d) (p Cr : ℝ), 2 < p → p ≤ 4 → Measurable r → Integrable r π →
        (∀ x, ‖centered π r x‖ ^ p ≤ Cr * lyap x) →
        ∃ V : S → Vec d, IsPoissonSolution P (centered π r) V ∧ GrowthBound lyap (1 / p) V) := by sorry

end MarkovCLTRate
