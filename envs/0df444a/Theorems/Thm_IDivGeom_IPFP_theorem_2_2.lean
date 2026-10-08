-- Prove2me | Theorems.Thm_IDivGeom_IPFP_theorem_2_2
-- name    : IDivGeom.IPFP.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:54:54.394612+00:00
-- url     : https://prove2.me/theorems/73f93b33-7f33-4b0e-bc71-6e0c951982a6
-- title:
--   Theorem 2.2 — Pythagorean characterization of I-projections
-- statement:
--   Let $\mathcal E$ be a convex set of probability distributions, let $R$ be a probability distribution, and let $Q\in\mathcal E$ have finite $I(Q\|R)$. Then $Q$ is the I-projection of $R$ on $\mathcal E$ exactly when every $P\in\mathcal E$ with finite $I(P\|R)$ satisfies $\int\log q_R\,dP\ge I(Q\|R)$; equivalently, exactly when
--
--   $$
--   I(P\|R)\ge I(P\|Q)+I(Q\|R)\qquad(P\in\mathcal E).
--   $$
--
--   If $Q$ is an algebraic inner point of $\mathcal E$, then every $P\in\mathcal E$ has finite $I(P\|R)$ and both displayed comparisons are equalities. Here algebraic inner means that for every $P\in\mathcal E$ there are $0<\alpha<1$ and $P'\in\mathcal E$ with $Q=\alpha P+(1-\alpha)P'$. The theorem supplies the projection identity used repeatedly in the cyclic argument.
--
--   **Formalization Note** The logarithmic integral takes values in extended reals and retains $\log0=-\infty$. The Pythagorean inequality uses $[0,\infty]$ and covers feasible $P$ with infinite divergence.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 150, Theorem 2.2 and (2.14) (PDF p. 5)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory
open scoped ENNReal

namespace IDivGeom.IPFP

theorem theorem_2_2 {X : Type*} [MeasurableSpace X]
    (ℰ : Set (Measure X)) (hℰ : ∀ P ∈ ℰ, IsProbabilityMeasure P)
    (hconv : IsConvexPD ℰ) (R : Measure X) [IsProbabilityMeasure R]
    (Q : Measure X) (hQ : Q ∈ ℰ) (hQR : klDiv Q R ≠ ⊤) :
    (IsIProjection R ℰ Q ↔
      ∀ P ∈ ℰ, klDiv P R ≠ ⊤ → ((klDiv Q R : ℝ≥0∞) : EReal) ≤ logDensInt R Q P) ∧
    (IsIProjection R ℰ Q ↔
      ∀ P ∈ ℰ, klDiv P Q + klDiv Q R ≤ klDiv P R) ∧
    (IsIProjection R ℰ Q → IsAlgInnerPoint ℰ Q →
      ∀ P ∈ ℰ, klDiv P R ≠ ⊤ ∧
        logDensInt R Q P = ((klDiv Q R : ℝ≥0∞) : EReal) ∧
        klDiv P R = klDiv P Q + klDiv Q R) := by sorry

end IDivGeom.IPFP
