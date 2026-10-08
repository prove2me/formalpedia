-- Prove2me | Theorems.Thm_IDivGeom_IPFP_eq_3_14
-- name    : IDivGeom.IPFP.eq_3_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:07:10.359357+00:00
-- url     : https://prove2.me/theorems/dcad306d-4ea4-48cd-8b69-3730e26df673
-- title:
--   Equation (3.14) — cumulative divergence identity
-- statement:
--   Let $\mathcal E_1,\ldots,\mathcal E_k$ be linear sets of probability distributions on a finite $X$, with nonempty intersection $\mathcal E$. Let $R$ be a probability distribution and assume some $P\in\mathcal E$ satisfies $P\ll R$. Start at $Q_0=R$, and obtain $Q_n$ by I-projecting $Q_{n-1}$ onto the cyclically selected set $\mathcal E_n$. Let $Q$ be the I-projection of $R$ onto $\mathcal E$.
--
--   For every $n\ge1$,
--
--   $$
--   I(Q\|R)=I(Q\|Q_n)+\sum_{i=1}^{n} I(Q_i\|Q_{i-1}).
--   $$
--
--   The identity accounts for the cumulative divergence cost of the successive projections and is the quantitative step in the convergence argument.
--
--   **Formalization Note** Lean indexes the first projection as `Qs 1` and the first set as `ℰ 0`; step $n+1$ uses `ℰ (n % k)`. The sequence predicate imposes the recursion, and $Q$ is required to be the actual I-projection.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 156, (3.14), proof of Theorem 3.2 (PDF p. 11)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory

namespace IDivGeom.IPFP

theorem eq_3_14 {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (k : ℕ) (hk : 0 < k) (ℰ : Fin k → Set (Measure X))
    (hlin : ∀ i, IsLinearPD (ℰ i)) (hne : (⋂ i, ℰ i).Nonempty)
    (R : Measure X) [IsProbabilityMeasure R]
    (hR : ∃ P ∈ ⋂ i, ℰ i, P ≪ R)
    (Qs : ℕ → Measure X) (hQs : IsCyclicIProjSeq hk ℰ R Qs)
    (Q : Measure X) (hQ : IsIProjection R (⋂ i, ℰ i) Q) :
    ∀ n, 0 < n →
      klDiv Q R = klDiv Q (Qs n) +
        ∑ i ∈ Finset.range n, klDiv (Qs (i + 1)) (Qs i) := by sorry

end IDivGeom.IPFP
