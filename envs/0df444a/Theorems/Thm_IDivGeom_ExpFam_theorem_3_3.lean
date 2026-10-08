-- Prove2me | Theorems.Thm_IDivGeom_ExpFam_theorem_3_3
-- name    : IDivGeom.ExpFam.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:50.763454+00:00
-- url     : https://prove2.me/theorems/11a20f80-4999-4943-aa89-6cb5f50181d1
-- title:
--   Theorem 3.3 — if T_R is open, the I-projection on ℰ(a) exists at every inner point of A_R and has density c·exp Σ tᵢfᵢ
-- statement:
--   Let $f_1,\dots,f_k$ be real-valued measurable functions on a measurable space $(X,\mathcal X)$ and $R$ a probability distribution on it. For $(a_1,\dots,a_k)\in E^k$ let $\mathcal E(a_1,\dots,a_k)$ be the set of PD's $P$ satisfying
--   $$\int f_i\,dP=a_i,\qquad i=1,\dots,k,$$
--   and let $A_R$ be the set of points $(a_1,\dots,a_k)\in E^k$ for which $\mathcal E(a_1,\dots,a_k)$ contains some $P$ with $I(P\|R)<\infty$. Suppose that
--   $$T_R=\Big\{(t_1,\dots,t_k):\ \exp\textstyle\sum_{i=1}^k t_i f_i(x)\ \text{is $R$-integrable}\Big\}$$
--   is an open set in $E^k$. Then for each inner point $(a_1,\dots,a_k)$ of $A_R$ the I-projection $Q$ of $R$ on $\mathcal E(a_1,\dots,a_k)$ exists, that is, $Q\in\mathcal E(a_1,\dots,a_k)$, $I(Q\|R)<\infty$ and $I(Q\|R)=\min_{P\in\mathcal E(a_1,\dots,a_k)}I(P\|R)$, and its $R$-density is of the exponential form
--   $$q_R(x)=c\exp\sum_{i=1}^k t_i f_i(x)\qquad(3.2)$$
--   for some constant $c$ and some $(t_1,\dots,t_k)\in E^k$.
--
--   This is the existence theorem for minimum-discrimination-information (maximum-entropy) distributions under moment constraints with possibly unbounded $f_i$: the constraint set is not closed in variation, so Theorem 2.1 does not apply, and the exponential form is obtained without Lagrange multipliers.
--
--   **Formalization Note** The I-divergence is Mathlib's `klDiv` (equal to (1.1) with the conventions (1.3) for PD's). "Inner point" is the topological interior of $A_R$ in $E^k$ = `Fin k → ℝ`; $k=0$ is allowed. The constraint $\int f_i\,dP=a_i$ includes $P$-integrability of $f_i$. The density formula holds $R$-almost everywhere, with no exceptional set of positive $R$-measure; $c$ is a real constant. (3.16) prints $(t_1,\dots,t_n)$, a misprint for $(t_1,\dots,t_k)$.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 156 (PDF 11), Theorem 3.3, with (3.16) on p. 156 and (3.2) on p. 151 (PDF 6)

import Mathlib
import Definitions.Def_IDivGeom_ExpFam_Setting

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.ExpFam

theorem theorem_3_3 {X : Type*} [MeasurableSpace X]
    (k : ℕ) (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i))
    (R : Measure X) [IsProbabilityMeasure R] (hT : IsOpen (expIntegrableSet f R)) :
    ∀ a ∈ interior (finiteSet f R), ∃ Q : Measure X, IDivGeom.IPFP.IsIProjection R (IDivGeom.IPFP.momentSet f a) Q ∧
      ∃ (c : ℝ) (t : Fin k → ℝ),
        ∀ᵐ x ∂ R, (Q.rnDeriv R x).toReal = c * Real.exp (∑ i, t i * f i x) := by sorry

end IDivGeom.ExpFam
