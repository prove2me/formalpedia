-- Prove2me | Theorems.Thm_IDivGeom_IPFP_theorem_3_2
-- name    : IDivGeom.IPFP.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:22.972985+00:00
-- url     : https://prove2.me/theorems/0dfaa0ae-58c0-4a87-a22c-18180bb56cb6
-- title:
--   Theorem 3.2 — convergence of cyclic I-projections
-- statement:
--   Let $X$ be a finite set, let $k\ge1$, and let $\mathcal E_1,\ldots,\mathcal E_k$ be linear sets of probability distributions whose intersection $\mathcal E$ is nonempty. Let $R$ be a probability distribution for which there exists $P\in\mathcal E$ with $P\ll R$. Starting at $Q_0=R$, form each $Q_n$ by I-projecting $Q_{n-1}$ onto $\mathcal E_n$, with the sets repeated cyclically. Such a sequence exists, and every sequence satisfying this recursion converges pointwise to the I-projection $Q$ of $R$ onto $\mathcal E$:
--
--   $$
--   Q_n(\{x\})\longrightarrow Q(\{x\})\qquad\text{for every }x\in X.
--   $$
--
--   On a finite set this is equivalently convergence in variation distance. The theorem identifies the limit of iterative proportional fitting under the paper’s finite-space and linear-set hypotheses.
--
--   **Formalization Note** The paper numbers the sets from $1$; Lean uses `Fin k`, so projection step `Qs (n+1)` uses `ℰ (n % k)`. The first conjunct asserts existence of the sequence, preventing a vacuous universal convergence claim. `IsIProjection` requires finite divergence and true minimization over the indicated set.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 155, Theorem 3.2 and (3.13) (PDF p. 10)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory Filter Topology

namespace IDivGeom.IPFP

theorem theorem_3_2 {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (k : ℕ) (hk : 0 < k) (ℰ : Fin k → Set (Measure X))
    (hlin : ∀ i, IsLinearPD (ℰ i)) (hne : (⋂ i, ℰ i).Nonempty)
    (R : Measure X) [IsProbabilityMeasure R]
    (hR : ∃ P ∈ ⋂ i, ℰ i, P ≪ R) :
    (∃ Qs : ℕ → Measure X, IsCyclicIProjSeq hk ℰ R Qs) ∧
    ∀ Qs : ℕ → Measure X, IsCyclicIProjSeq hk ℰ R Qs →
      ∃ Q, IsIProjection R (⋂ i, ℰ i) Q ∧
        ∀ x : X, Tendsto (fun n => (Qs n).real {x}) atTop (𝓝 (Q.real {x})) := by sorry

end IDivGeom.IPFP
