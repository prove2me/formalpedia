-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_submodular_extension
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.submodular_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:56:25.816962+00:00
-- url     : https://prove2.me/theorems/5d186e74-15c6-445d-8608-a5525e84fa50
-- title:
--   Theorem 6.4 — offline DP, 2-competitive and e/(e−1)-competitive timers for submodular service costs
-- statement:
--   Consider any submodular service-cost model (Definition 6.1) under the maximum-delay objective. Then:
--
--   1. the abstract dynamic program based on recurrence (2) returns, on every finite input, the optimal value $\mathrm{OPT}(I)$ and a feasible schedule of cost $\mathrm{OPT}(I)$;
--   2. OPT-Timer(1) is an online algorithm, feasible on every input, with $\mathrm{ALG}(I)\le 2\,\mathrm{OPT}(I)$ for every input;
--   3. sampling one global parameter $\Theta$ from the density $f(x)=e^x/(e-1)$ on $[0,1]$ (equation (17)) and running OPT-Timer($\Theta$) is $e/(e-1)$-competitive against an oblivious adversary: for every $\theta\in[0,1]$, OPT-Timer($\theta$) is online and feasible, its cost is measurable in $\theta$, and for every input $I$ fixed independently of $\Theta$,
--   $$\mathbb E[\mathrm{ALG}(I)]=\int_0^1 \mathrm{ALG}_\theta(I)\,f(\theta)\,d\theta\le\frac{e}{e-1}\,\mathrm{OPT}(I).$$
--
--   So the offline algorithm and both online guarantees of the tree case extend to every submodular service-cost model.
--
--   Differences from the source:
--   - encoding: Definition 6.1: a universe U of labelled occurrences, κ on finite sets, service objects → a structure SubmodularModel U Obj over arbitrary types U and Obj, with κ : Finset U → ℝ and the published diminishing-returns submodularity predicate; reason: on finite sets diminishing returns is equivalent to κ(A)+κ(B) ≥ κ(A∪B)+κ(A∩B); nonnegativity follows from κ(∅)=0 and monotonicity
--   - reading: a service object 'has no effect on the availability or cost of later services'; an attaining object 'can be executed at time t ≥ max a(r)' → an object's cleared batch and spatial cost are functions of the object and the current pending set only, and every object can be executed at every time; reason: this is the history independence the definition states; Section 6 imposes no other time restriction
--   - encoding: costs in ℝ with +∞ for an infeasible schedule; OPT the minimum over feasible offline schedules → ℝ≥0∞ costs, ⊤ for infeasible, OPT the infimum over all finite schedules (published cost and optimum); reason: the same values; attainment is part of the base milestones
--   - encoding: Θ sampled according to (17) → the published seedLaw (Lebesgue measure on [0,1] with density e^x/(e−1)) and the lower integral of the cost; reason: the base mission's law; measurability of θ ↦ cost is concluded, so the integral is the expectation
--   - encoding: 2- and e/(e−1)-competitive → causality, feasibility and a strictly multiplicative bound in ℝ≥0∞ for every input; reason: Section 2's definitions, with the input chosen outside the integral
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), pp. 16–17, Theorem 6.4 and its proof; p. 13, equation (17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_SubmodularTimer
import Definitions.Def_MLAMaxDelay_RandomizedTimer_RandomLaw

namespace MLAMaxDelay.RandomizedTimer.Supplement

open MeasureTheory

/-- Theorem 6.4, pp. 16–17, all three clauses, for every submodular service-cost model and every
finite input. The input of (iii) is fixed outside the integral over the published seed law (17):
the adversary is oblivious. All ratios are strictly multiplicative. -/
theorem submodular_extension {U Obj : Type} [DecidableEq U] (M : SubmodularModel U Obj) :
    -- (i) the abstract dynamic program
    (∀ I : Finset U,
      (smOffline M I).value = smOptimumReal M I ∧
      ENNReal.ofReal (smOffline M I).value = smOptimum M I ∧
      SMFeasible M I (smOffline M I).schedule ∧
      smCost M I (smOffline M I).schedule = smOptimum M I) ∧
    -- (ii) OPT-Timer(1) is deterministically 2-competitive
    (SMCausal M (fun I => smOptTimer M I 1) ∧
      ∀ I : Finset U, SMFeasible M I (smOptTimer M I 1) ∧
        smCost M I (smOptTimer M I 1) ≤ 2 * smOptimum M I) ∧
    -- (iii) OPT-Timer(Θ) with Θ drawn from (17) is e/(e−1)-competitive
    ((∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → SMCausal M (fun I => smOptTimer M I θ)) ∧
      ∀ I : Finset U,
        (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → SMFeasible M I (smOptTimer M I θ)) ∧
        Measurable (fun θ => smCost M I (smOptTimer M I θ)) ∧
        ∫⁻ θ, smCost M I (smOptTimer M I θ) ∂seedLaw ≤
          ENNReal.ofReal (Real.exp 1 / (Real.exp 1 - 1)) * smOptimum M I) := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
