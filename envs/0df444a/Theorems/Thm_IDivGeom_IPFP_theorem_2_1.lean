-- Prove2me | Theorems.Thm_IDivGeom_IPFP_theorem_2_1
-- name    : IDivGeom.IPFP.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:51.025264+00:00
-- url     : https://prove2.me/theorems/a2c16ed6-b92e-4feb-bc34-0b0f8adbf395
-- title:
--   Theorem 2.1 — existence of an I-projection on a variation-closed convex set
-- statement:
--   Let $\mathcal E$ be a convex set of probability distributions on a measurable space, closed under convergence in variation distance, and let $R$ be a probability distribution. If $\mathcal E$ contains a distribution $P$ with finite $I(P\|R)$, then there is a distribution $Q\in\mathcal E$ such that
--
--   $$
--   I(Q\|R)<\infty,\qquad I(Q\|R)\le I(P'\|R)\quad\text{for every }P'\in\mathcal E.
--   $$
--
--   Thus a finite I-projection exists whenever the feasible set meets the finite-divergence I-sphere. This gives the existence result used for linear constraints on finite spaces.
--
--   **Formalization Note** Variation closure is expressed sequentially through the variation distance of (1.6).
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 148, Theorem 2.1 (PDF p. 3)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory

namespace IDivGeom.IPFP

theorem theorem_2_1 {X : Type*} [MeasurableSpace X]
    (ℰ : Set (Measure X)) (hℰ : ∀ P ∈ ℰ, IsProbabilityMeasure P)
    (hconv : IsConvexPD ℰ) (hclosed : IsVarClosed ℰ)
    (R : Measure X) [IsProbabilityMeasure R]
    (hR : ∃ P ∈ ℰ, klDiv P R ≠ ⊤) :
    ∃ Q, IsIProjection R ℰ Q := by sorry

end IDivGeom.IPFP
