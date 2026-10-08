-- Prove2me | Theorems.Thm_IDivGeom_IPFP_theorem_2_3
-- name    : IDivGeom.IPFP.theorem_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:54:57.420168+00:00
-- url     : https://prove2.me/theorems/e14fa630-6b6a-41b0-be34-c1b9249e4752
-- title:
--   Theorem 2.3 — transitivity of I-projections
-- statement:
--   Let $\mathcal E_1\subseteq\mathcal E$ be convex sets of probability distributions. Suppose $Q$ is the I-projection of $R$ on $\mathcal E$, $Q_1$ is the I-projection of $R$ on $\mathcal E_1$, and the exact Pythagorean identity holds throughout $\mathcal E$:
--
--   $$
--   I(P\|R)=I(P\|Q)+I(Q\|R)\qquad(P\in\mathcal E).
--   $$
--
--   Then $Q_1$ is the I-projection of $Q$ on $\mathcal E_1$. This transitivity identifies the intersection projection after successive projections onto the larger sets.
--
--   **Formalization Note** The paper’s $\subset$ is read as subset inclusion, without requiring proper inclusion.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 151, Theorem 2.3 (PDF p. 6)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory

namespace IDivGeom.IPFP

theorem theorem_2_3 {X : Type*} [MeasurableSpace X]
    (ℰ ℰ₁ : Set (Measure X)) (hℰ : ∀ P ∈ ℰ, IsProbabilityMeasure P)
    (h1 : ℰ₁ ⊆ ℰ) (hconv : IsConvexPD ℰ) (hconv1 : IsConvexPD ℰ₁)
    (R : Measure X) [IsProbabilityMeasure R] (Q Q₁ : Measure X)
    (hQ : IsIProjection R ℰ Q) (hQ1 : IsIProjection R ℰ₁ Q₁)
    (h17 : ∀ P ∈ ℰ, klDiv P R = klDiv P Q + klDiv Q R) :
    IsIProjection Q ℰ₁ Q₁ := by sorry

end IDivGeom.IPFP
