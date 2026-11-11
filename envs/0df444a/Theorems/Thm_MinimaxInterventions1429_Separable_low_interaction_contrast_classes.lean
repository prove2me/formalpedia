-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_low_interaction_contrast_classes
-- name    : MinimaxInterventions1429.Separable.low_interaction_contrast_classes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:20.11621+00:00
-- url     : https://prove2.me/theorems/ac2368ed-65d3-4fb5-a08f-540f9e34b9e7
-- title:
--   Theorem 4.2 — contrast classes at low interaction
-- statement:
--   Let $m,k\ge2$, $L\in[0,1]^{m\times k}$, and $\alpha\ge\Lambda(L)$. Define $\omega_{gh}=L_{gh}-L_{g1}$, $\mathcal C(L)=\{M\in[0,1]^{m\times k}:\omega(M)=\omega(L)\}$, and $\rho(L)=\tfrac14\max_{g\ne r}(2-\operatorname{span}_g(L)-\operatorname{span}_r(L))$. There is one measurable pure-action response map that is $\alpha$-optimal for $M+B$ for every $M\in\mathcal C(L)$ and every real separable $B$, without a bound on its norm. Moreover,
--
--   $$\operatorname{diam}_{d_q}\mathcal C(L)=2\rho(L),\qquad
--   \operatorname{rad}_{d_q}\mathcal C(L)=\rho(L).$$
--
--   The diameter is attained by two members; a radius-$\rho(L)$ center belongs to the class. There exists $L'\in\mathcal C(L)$ with $d_q(L,L')\ge\rho(L)$. For every randomized procedure, even with complete numerical responses and no query limit, the common map forces error at least $\rho(L)$ with probability at least $1/2$ on some member of the class. No procedure can have error strictly below $\rho(L)/2$ on both $L$ and $L'$ with probability greater than $1/2$ on each. The hard member can depend on the procedure and its random-seed law, but not on the realized seed.
--
--   The radius statement allows all real tables as centers. Failure counts as unsuccessful, and $\rho(L)=0$ remains in scope. These conclusions give the exact low-interaction ambiguity, not merely a two-table existence bound.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
--   - encoding: possibly randomized procedures, with all events and transcripts measurable → arbitrary probability spaces for random seeds, measurable common response maps and exact bit kernels, and explicit measurable output or success-event conditions; probabilities in ENNReal; reason: these are Section 2 standing measurability conventions, not restrictions to finite seeds, rational queries or fixed tie-breaking
--   - encoding: procedures reading complete mixtures with unboundedly many queries → measurable seed-dependent estimators of the entire common numerical response map; reason: every observable-history procedure induces such an estimator; the fixed common map is independent of the hidden table and seed, and gives exactly the same observation on the hard inputs
--   - encoding: quotient diameter 2 rho and Chebyshev radius rho → real supremum and infimum definitions together with explicit attaining diameter witnesses and a center in the contrast class; reason: these are the extrema established on the nonempty compact class in the source proof; no attainment is assumed
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 4.2, printed p.15 (PDF p.17)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem low_interaction_contrast_classes {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (L : Table m k) (hL : InCube L)
    (α : ℝ) (hα : interaction L ≤ α) :
    classDiameter L = 2 * ambiguityRadius L ∧ classRadius L = ambiguityRadius L ∧
    (∃ C ∈ contrastClass L, ∀ M ∈ contrastClass L, quotientDist C M ≤ ambiguityRadius L) ∧
    (∃ M ∈ contrastClass L, ∃ N ∈ contrastClass L,
      quotientDist M N = 2 * ambiguityRadius L) ∧
    ∃ L' ∈ contrastClass L, ambiguityRadius L ≤ quotientDist L L' ∧
      ∃ p : Table m k → Mixture k, Measurable p ∧
        (∀ B, Pure (p B)) ∧
        (∀ M ∈ contrastClass L, ∀ B, IsSeparable B → Optimal (M + B) α (p B)) ∧
        (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure μ] (A : FullLearner Ω m k),
          Measurable (fun s => A s p) →
          (∃ M ∈ contrastClass L,
            (1 / 2 : ENNReal) ≤ μ {s | ErrorAtLeast M (ambiguityRadius L) (A s p)}) ∧
          ¬ ((1 / 2 : ENNReal) < μ {s | StrictlyWithin L (ambiguityRadius L / 2) (A s p)} ∧
             (1 / 2 : ENNReal) < μ {s | StrictlyWithin L' (ambiguityRadius L / 2) (A s p)}))
    := by sorry

end MinimaxInterventions1429.Separable
