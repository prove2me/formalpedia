-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_available_interaction_identification
-- name    : MinimaxInterventions1429.Separable.Supplement.available_interaction_identification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:17:31.039199+00:00
-- url     : https://prove2.me/theorems/a6882880-e56c-4892-ab9a-60241069df35
-- title:
--   Theorem 1.3 — Available interaction and universal identification
-- statement:
--   Let $m,k\ge2$, $\alpha\ge0$, $T\ge1$, and let $K$ be a nonempty compact public control set with norm bound $\tau$. A public maximizer of $\Xi(K)$ is supplied. If $K=-K$, the fixed two-shift algorithm uses at most $2(mk-1)T$ one-bit queries in $Q_K$, each of norm at most $5+11\tau$. Against every history-dependent realized accurate transcript, every returned table has
--   $$d_q(\widehat L,L)\le17\alpha+\tfrac{17}{2}D_\tau2^{-T},$$
--   and a table is returned whenever $\Xi(K)>44\alpha+18D_\tau2^{-T}$.
--
--   Conversely, without symmetry, if $\alpha\ge\Xi(K)$, one pure response map is $\alpha$-optimal for every row-constant cube table on $Q_K$. For every randomized learner, even one given the complete numerical response map, some fixed row-constant table has error at least $1/2$ with probability at least $1/2$. Failure counts as error. This separates universal recovery from public-control ambiguity.
--
--   Differences from the source:
--   - encoding: the two-run algorithm and arbitrary randomized procedures → a fixed adaptive bit program and a learner granted the entire common numerical map; reason: realized-history accuracy handles adaptive replies; the hard table is chosen after the learner but independently of its seed
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 1.3, printed p.3 (PDF p.5)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Interfaces
set_option autoImplicit false
universe u_available_interaction_identification

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem available_interaction_identification
    {m k : ℕ} [NeZero m] [NeZero k] (hm : 2 ≤ m) (hk : 2 ≤ k)
    (K : Set (Table m k)) (τ α : ℝ) (hK : ControlSet K τ) (hα : 0 ≤ α) :
    (symmetricControls K → ∀ C ∈ K, interaction C = availableInteraction K → ∀ T : ℕ, 1 ≤ T →
      (twoShift C τ α T).maxQueries ≤ 2*(m*k-1)*T ∧
      (twoShift C τ α T).queriesSatisfy (fun q => q.surcharge ∈ controlQueries K τ ∧
        entryNorm q.surcharge ≤ 5+11*τ) ∧
      ∀ (L : Table m k) (O : BitOracle m k), InCube L →
        AccurateHistory L α ((twoShift C τ α T).run O []).2 →
        (∀ M, ((twoShift C τ α T).run O []).1 = some M →
          quotientDist M L ≤ 17*α+(17/2)*dilation τ*eta T) ∧
        (44*α+18*dilation τ*eta T < availableInteraction K →
          ∃ M, ((twoShift C τ α T).run O []).1 = some M)) ∧
    (availableInteraction K ≤ α →
      ∃ p : Table m k → Mixture k,
        (∀ (a : Fin m → ℝ), (∀ g, 0 ≤ a g ∧ a g ≤ 1) →
          ∀ Q ∈ controlQueries K τ, Pure (p Q) ∧ Optimal (rowConstant a + Q) α (p Q)) ∧
        ∀ (Ω : Type u_available_interaction_identification) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (learner : FullLearner Ω m k),
          (∀ a : Fin m → ℝ, MeasurableSet {s | ErrorAtLeast (rowConstant a) (1/2) (learner s p)}) →
          ∃ a : Fin m → ℝ, (∀ g, 0 ≤ a g ∧ a g ≤ 1) ∧
            ENNReal.ofReal (1/2) ≤ μ {s | ErrorAtLeast (rowConstant a) (1/2) (learner s p)}) := by sorry

end MinimaxInterventions1429.Separable.Supplement
