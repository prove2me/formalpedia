-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_local_two_table_error_floor
-- name    : MinimaxInterventions1429.Separable.local_two_table_error_floor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:05.545225+00:00
-- url     : https://prove2.me/theorems/2ea4ede1-3f59-4173-acd2-420fbbe89c95
-- title:
--   Proposition 4.1 — local two-table error floor
-- statement:
--   Let $m,k\ge2$, $L\in[0,1]^{m\times k}$, and $0<\alpha\le1/4$. There is $L'\in[0,1]^{m\times k}$ and one measurable numerical response map $p$ on all real surcharge matrices such that
--
--   $$d_q(L,L')=\alpha,\qquad |\Lambda(L')-\Lambda(L)|\le2\alpha,$$
--
--   and $p(B)$ is $\alpha$-optimal for both $L+B$ and $L'+B$ for every real $B$, whether separable or not. Consequently no randomized procedure observing these responses can achieve quotient error strictly below $\alpha/2$ on both tables with probability greater than $1/2$ on each. The procedure can read complete mixtures, use any number of queries, and have any probability law on its private random seed.
--
--   The common response map and neighbor are selected independently of that seed. This is a local error floor around every cube table, including its boundary, together with the required control on interaction.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
--   - encoding: possibly randomized procedures, with all events and transcripts measurable → arbitrary probability spaces for random seeds, measurable common response maps and exact bit kernels, and explicit measurable output or success-event conditions; probabilities in ENNReal; reason: these are Section 2 standing measurability conventions, not restrictions to finite seeds, rational queries or fixed tie-breaking
--   - encoding: procedures reading complete mixtures with unboundedly many queries → measurable seed-dependent estimators of the entire common numerical response map; reason: every observable-history procedure induces such an estimator; the fixed common map is independent of the hidden table and seed, and gives exactly the same observation on the hard inputs
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Proposition 4.1, printed p.14 (PDF p.16)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem local_two_table_error_floor {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (L : Table m k) (hL : InCube L)
    (α : ℝ) (hα : 0 < α) (hαu : α ≤ 1 / 4) :
    ∃ L' : Table m k, InCube L' ∧ quotientDist L L' = α ∧
      |interaction L' - interaction L| ≤ 2 * α ∧
      ∃ p : Table m k → Mixture k, Measurable p ∧
        (∀ B, Optimal (L + B) α (p B) ∧ Optimal (L' + B) α (p B)) ∧
        (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure μ] (A : FullLearner Ω m k),
          Measurable (fun s => A s p) →
          ¬ ((1 / 2 : ENNReal) < μ {s | StrictlyWithin L (α / 2) (A s p)} ∧
             (1 / 2 : ENNReal) < μ {s | StrictlyWithin L' (α / 2) (A s p)})) := by sorry

end MinimaxInterventions1429.Separable
