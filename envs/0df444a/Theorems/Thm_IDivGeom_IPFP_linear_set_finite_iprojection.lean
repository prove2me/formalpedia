-- Prove2me | Theorems.Thm_IDivGeom_IPFP_linear_set_finite_iprojection
-- name    : IDivGeom.IPFP.linear_set_finite_iprojection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:06:58.98899+00:00
-- url     : https://prove2.me/theorems/3548b601-5fd2-4f13-9668-4eff851978d8
-- title:
--   Proof of Theorem 3.2 — finite linear-set projection and identity
-- statement:
--   Let $X$ be finite and $\mathcal E$ a linear set of probability distributions on $X$: every real affine combination of two of its members that remains a probability distribution also belongs to $\mathcal E$. If a feasible $P$ satisfies $P\ll R$, then the I-projection $Q$ of $R$ on $\mathcal E$ exists, and
--
--   $$
--   I(P'\|R)=I(P'\|Q)+I(Q\|R)\qquad(P'\in\mathcal E).
--   $$
--
--   This is the existence and exact identity asserted at the start of the proof of Theorem 3.2. It is the finite-dimensional bridge from the earlier geometric results to the cyclic algorithm.
--
--   **Formalization Note** On finite $X$, absolute continuity is equivalent to finite I-divergence. Singleton measurability makes point masses measurable.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 155, proof of Theorem 3.2 (PDF p. 10)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory

namespace IDivGeom.IPFP

theorem linear_set_finite_iprojection {X : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (ℰ : Set (Measure X)) (hlin : IsLinearPD ℰ)
    (R : Measure X) [IsProbabilityMeasure R]
    (hR : ∃ P ∈ ℰ, P ≪ R) :
    ∃ Q, IsIProjection R ℰ Q ∧
      ∀ P ∈ ℰ, klDiv P R = klDiv P Q + klDiv Q R := by sorry

end IDivGeom.IPFP
