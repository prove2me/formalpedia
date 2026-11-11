-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_reconstruction_under_separable_interventions
-- name    : MinimaxInterventions1429.Separable.reconstruction_under_separable_interventions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:28.996765+00:00
-- url     : https://prove2.me/theorems/f5df43a6-3f46-4831-8c8b-6f4bc14a64d3
-- title:
--   Theorem 1.1 — reconstruction under separable interventions (a)–(e)
-- statement:
--   Let $m,k\ge2$, $\alpha\ge0$, and integer $T\ge1$. Hidden tables range over the entire closed cube $[0,1]^{m\times k}$. For a real table $M$, use $F_M(p)=\max_g\sum_hM_{gh}p_h$ on the closed simplex, and quotient distance $d_q(M,L)=\inf_\lambda\max_{g,h}|M_{gh}-L_{gh}-\lambda|$. Write $\omega_{gh}=L_{gh}-L_{g1}$, $\Lambda(L)=\max_h(\max_g\omega_{gh}-\min_g\omega_{gh})$, $s_g=\max_hL_{gh}-\min_hL_{gh}$, $\rho(L)=\tfrac14\max_{g\ne r}(2-s_g-s_r)$, and $\mathcal C(L)=\{M\in[0,1]^{m\times k}:\omega(M)=\omega(L)\}$. All five conclusions of Theorem 1.1 hold:
--
--   1. The fixed deterministic Section 3.2 algorithm makes at most $(mk-1)T$ one-bit queries with separable surcharges of max-entry norm at most $5$. Under arbitrary history-dependent $\alpha$-accurate realized answers, every returned table satisfies
--      $$d_q(\widehat L,L)\le17\alpha+\tfrac{17}{2}2^{-T}.$$
--      A table is returned whenever $\Lambda(L)>44\alpha+18\cdot2^{-T}$; otherwise failure is permitted.
--   2. Its very same first $m(k-1)T$ queries give the contrast-only estimator, for every table without an interaction promise, with
--      $$d_q(\widehat L^{\mathrm{contrast}},L)\le\rho(L)+4\alpha+2^{1-T}.$$
--   3. If $\Lambda(L)\le\alpha$, a single measurable pure-action map is $\alpha$-optimal for $M+B$ simultaneously for all $M\in\mathcal C(L)$ and all real separable surcharges $B$. The class has quotient diameter $2\rho(L)$. Every procedure then has error at least $\rho(L)$ with probability at least $1/2$ on some member, even with the complete response map and arbitrary random seeds.
--   4. If $0<\alpha\le1/4$, every $L$ has a neighbor $L'$ in the cube with $d_q(L,L')=\alpha$ and $|\Lambda(L')-\Lambda(L)|\le2\alpha$, sharing an $\alpha$-optimal response map for every real surcharge, including nonseparable ones.
--   5. With exact bit answers, any randomized algorithm that returns quotient error at most $0<\gamma\le1/128$ with probability at least $2/3$ on every cube table with $\Lambda\ge1/8$ and against every exact oracle must satisfy
--      $$Q\ge(mk-1)\log_2\!\frac1{128\gamma}-\log_2\!\frac32,$$
--      where $Q$ bounds calls on every branch.
--
--   This goal combines reconstruction, the available contrast prefix, both ambiguity regimes, and the exact one-bit query cost. Outputs are arbitrary real tables; failure never counts as a successful estimate. Accuracy uses a separate existential mixture witness for each bit and allows both bits at a threshold tie.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
--   - encoding: adversarial bit answers accurate only along the realized calls → a finite bit-query program evaluated with an arbitrary history-dependent oracle and a witness for each recorded bit; reason: the program observes only bits and public queries; weak ties admit both bits and no common witness or numerical response is assumed
--   - encoding: possibly randomized procedures, with all events and transcripts measurable → arbitrary probability spaces for random seeds, measurable common response maps and exact bit kernels, and explicit measurable output or success-event conditions; probabilities in ENNReal; reason: these are Section 2 standing measurability conventions, not restrictions to finite seeds, rational queries or fixed tie-breaking
--   - encoding: procedures reading complete mixtures with unboundedly many queries → measurable seed-dependent estimators of the entire common numerical response map; reason: every observable-history procedure induces such an estimator; the fixed common map is independent of the hidden table and seed, and gives exactly the same observation on the hard inputs
--   - encoding: part (b) uses the same initial queries as part (a) → literal contrast-phase evaluation, exact query count and prefix relation in the concrete reconstruction; reason: no independent estimator or additional oracle calls are substituted
--   - generalization: the baseline query family in Section 2 is bounded and separable → the query program may use arbitrary real surcharge matrices; reason: the source packing and binary-tree counting proof does not use any intervention restriction; restricting queries recovers the baseline result
--   - encoding: real base-two logarithmic bound on the natural query budget Q → Q cast to the reals and log x divided by log 2; reason: gamma is positive and at most 1/128, so all logarithms and divisions have the source domain
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 1.1(a)–(e), printed p.2 (PDF p.4); explicit proof printed p.16 (PDF p.18)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem reconstruction_under_separable_interventions {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (α : ℝ) (hα : 0 ≤ α) (T : ℕ) (hT : 1 ≤ T) :
    (reconstruction m k α T).maxQueries ≤ (m * k - 1) * T ∧
    (reconstruction m k α T).queriesSatisfy (fun q => Allowed q.surcharge) ∧
    (∀ (L : Table m k), InCube L → ∀ O : BitOracle m k,
      AccurateHistory L α ((reconstruction m k α T).run O []).2 →
      (∀ g M, ((reconstruction m k α T).run O []).1 = some (g, M) →
        quotientDist M L ≤ 17 * α + (17 : ℝ) / 2 * eta T) ∧
      (44 * α + 18 * eta T < interaction L →
        ∃ g M, ((reconstruction m k α T).run O []).1 = some (g, M))) ∧
    ((contrastPhase m k α T).maxQueries = m * (k - 1) * T ∧
      ∀ (L : Table m k), InCube L → ∀ O : BitOracle m k,
      (((contrastPhase m k α T).run O []).2).IsPrefix
        (((reconstruction m k α T).run O []).2) ∧
      (AccurateHistory L α ((contrastPhase m k α T).run O []).2 →
        quotientDist ((contrastEstimate m k α T).run O []).1 L ≤
          ambiguityRadius L + 4 * α + 2 * eta T)) ∧
    (∀ L : Table m k, InCube L → interaction L ≤ α →
      classDiameter L = 2 * ambiguityRadius L ∧
      ∃ p : Table m k → Mixture k, Measurable p ∧
        (∀ B, Pure (p B)) ∧
        (∀ M ∈ contrastClass L, ∀ B, IsSeparable B → Optimal (M + B) α (p B)) ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure μ] (A : FullLearner Ω m k),
          Measurable (fun s => A s p) →
          ∃ M ∈ contrastClass L,
            (1 / 2 : ENNReal) ≤ μ {s | ErrorAtLeast M (ambiguityRadius L) (A s p)}) ∧
    (∀ L : Table m k, InCube L → 0 < α → α ≤ 1 / 4 →
      ∃ L' : Table m k, InCube L' ∧ quotientDist L L' = α ∧
        |interaction L' - interaction L| ≤ 2 * α ∧
        ∃ p : Table m k → Mixture k, Measurable p ∧
          ∀ B, Optimal (L + B) α (p B) ∧ Optimal (L' + B) α (p B)) ∧
    (∀ (γ : ℝ), 0 < γ → γ ≤ 1 / 128 → ∀ (Q : ℕ)
      {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (A : Ω → BitProgram m k (Option (Table m k))),
      (∀ s, (A s).maxQueries ≤ Q) →
      (∀ (L : Table m k) (O : BitOracle m k),
        ExactOracle L O → MeasurableSet {s | Within L γ ((A s).run O []).1}) →
      (∀ L : Table m k, InCube L → (1 : ℝ) / 8 ≤ interaction L →
        ∀ O : BitOracle m k, ExactOracle L O →
        (2 / 3 : ENNReal) ≤ μ {s | Within L γ ((A s).run O []).1}) →
      ((m * k - 1 : ℕ) : ℝ) * (Real.log (1 / (128 * γ)) / Real.log 2) -
        Real.log ((3 : ℝ) / 2) / Real.log 2 ≤ (Q : ℝ)) := by sorry

end MinimaxInterventions1429.Separable
