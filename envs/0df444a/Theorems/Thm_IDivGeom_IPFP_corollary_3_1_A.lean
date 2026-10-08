-- Prove2me | Theorems.Thm_IDivGeom_IPFP_corollary_3_1_A
-- name    : IDivGeom.IPFP.corollary_3_1_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:06:21.833226+00:00
-- url     : https://prove2.me/theorems/b6bd1a36-92c1-4f2d-8c0f-184cd7dd51d6
-- title:
--   Corollary 3.1(A) — exponential density under finite moment constraints
-- statement:
--   Fix measurable real functions $f_1,\ldots,f_k$ and real targets $a_1,\ldots,a_k$. Let $\mathcal E$ be the probability distributions $P$ for which every $f_i$ is integrable and $\int f_i\,dP=a_i$. For a given probability distribution $R$ and $Q\in\mathcal E$, $Q$ is its I-projection onto $\mathcal E$ exactly when, outside an exceptional measurable set $N$ ignored by every $P\in\mathcal E$ with finite $I(P\|R)$, its density has the form
--
--   $$
--   q_R(x)=c\exp\!\left(\sum_{i=1}^{k}t_i f_i(x)\right),\quad x\notin N;\qquad q_R(x)=0,\quad x\in N.
--   $$
--
--   Whenever $Q$ is the I-projection, $I(P\|R)=I(P\|Q)+I(Q\|R)$ for all $P\in\mathcal E$. If some finite-divergence feasible $P$ is equivalent to $R$, the exceptional set can be removed: the pure exponential form is necessary and sufficient.
--
--   **Formalization Note** Integrability is explicit to prevent Lean’s default zero integral for nonintegrable functions. A density formula presupposes $Q\ll R$; this is explicit in both equivalences, since `rnDeriv` alone does not describe a singular part. Equality of densities is $R$-almost everywhere.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 152, Corollary 3.1, case (A) (PDF p. 7)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory

namespace IDivGeom.IPFP
attribute [local instance] Classical.propDecidable

theorem corollary_3_1_A {X : Type*} [MeasurableSpace X]
    (k : ℕ) (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i))
    (a : Fin k → ℝ) (R : Measure X) [IsProbabilityMeasure R]
    (Q : Measure X) (hQ : Q ∈ momentSet f a) :
    (IsIProjection R (momentSet f a) Q ↔
      Q ≪ R ∧ ∃ (c : ℝ) (t : Fin k → ℝ) (N : Set X),
        MeasurableSet N ∧
        (∀ P ∈ momentSet f a, klDiv P R ≠ ⊤ → P N = 0) ∧
        ∀ᵐ x ∂ R, (Q.rnDeriv R x).toReal =
          if x ∈ N then 0 else c * Real.exp (∑ i, t i * f i x)) ∧
    (IsIProjection R (momentSet f a) Q →
      ∀ P ∈ momentSet f a, klDiv P R = klDiv P Q + klDiv Q R) ∧
    ((∃ P ∈ momentSet f a, klDiv P R ≠ ⊤ ∧ P ≪ R ∧ R ≪ P) →
      (IsIProjection R (momentSet f a) Q ↔
        Q ≪ R ∧ ∃ (c : ℝ) (t : Fin k → ℝ),
          ∀ᵐ x ∂ R, (Q.rnDeriv R x).toReal =
            c * Real.exp (∑ i, t i * f i x))) := by sorry

end IDivGeom.IPFP
