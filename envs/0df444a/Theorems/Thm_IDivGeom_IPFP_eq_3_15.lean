-- Prove2me | Theorems.Thm_IDivGeom_IPFP_eq_3_15
-- name    : IDivGeom.IPFP.eq_3_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:08:46.326663+00:00
-- url     : https://prove2.me/theorems/763da237-fdbb-4050-aa0b-734b116eb9d6
-- title:
--   Equation (3.15) — identity at each cyclic iterate
-- statement:
--   Let $\mathcal E_1,\ldots,\mathcal E_k$ be linear sets of probability distributions on a finite $X$, with nonempty intersection $\mathcal E$. Let $R$ be a probability distribution and assume some $P\in\mathcal E$ satisfies $P\ll R$. Start at $Q_0=R$, and obtain $Q_n$ by I-projecting $Q_{n-1}$ onto the cyclically selected set $\mathcal E_n$. Let $Q$ be the I-projection of $R$ onto $\mathcal E$.
--
--   For every $n\ge1$ and every $P\in\mathcal E$,
--
--   $$
--   I(P\|Q_n)=I(P\|Q)+I(Q\|Q_n).
--   $$
--
--   This identity identifies the projection onto the intersection from every iterate and is used to rule out an incorrect subsequential limit.
--
--   **Formalization Note** The Lean sequence starts at `Qs 0 = R`; step $n+1$ projects onto `ℰ (n % k)`. The claim is stated only for $n\ge1$, exactly as on the page.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 156, (3.15), proof of Theorem 3.2 (PDF p. 11)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory

namespace IDivGeom.IPFP

theorem eq_3_15 {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (k : ℕ) (hk : 0 < k) (ℰ : Fin k → Set (Measure X))
    (hlin : ∀ i, IsLinearPD (ℰ i)) (hne : (⋂ i, ℰ i).Nonempty)
    (R : Measure X) [IsProbabilityMeasure R]
    (hR : ∃ P ∈ ⋂ i, ℰ i, P ≪ R)
    (Qs : ℕ → Measure X) (hQs : IsCyclicIProjSeq hk ℰ R Qs)
    (Q : Measure X) (hQ : IsIProjection R (⋂ i, ℰ i) Q) :
    ∀ n, 0 < n → ∀ P ∈ ⋂ i, ℰ i,
      klDiv P (Qs n) = klDiv P Q + klDiv Q (Qs n) := by sorry

end IDivGeom.IPFP
