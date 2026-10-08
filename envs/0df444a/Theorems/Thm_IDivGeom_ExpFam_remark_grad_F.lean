-- Prove2me | Theorems.Thm_IDivGeom_ExpFam_remark_grad_F
-- name    : IDivGeom.ExpFam.remark_grad_F
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:40.949134+00:00
-- url     : https://prove2.me/theorems/70f3a676-a2dd-4493-a180-9879e663be50
-- title:
--   Remark after Theorem 3.3 — F is differentiable at inner points of A_R with gradient the parameter vector of (3.2)
-- statement:
--   Let $f_1,\dots,f_k$ be real-valued measurable functions on $(X,\mathcal X)$, $R$ a PD, and suppose that the set $T_R$ of (3.16) is open in $E^k$. Let $(a_1,\dots,a_k)$ be an inner point of $A_R$, and let $Q$ be the I-projection of $R$ on $\mathcal E(a_1,\dots,a_k)$ with $R$-density
--   $$q_R(x)=c\exp\sum_{i=1}^k t_i f_i(x)\qquad(3.2).$$
--   Then the function $F$ of (3.18) is differentiable at $(a_1,\dots,a_k)$ and
--   $$\operatorname{grad}F(a_1,\dots,a_k)=(t_1,\dots,t_k).$$
--
--   Thus the natural parameters of the exponential-family form of the I-projection are the partial derivatives of the optimal value with respect to the constraint levels, the sensitivity interpretation familiar from Lagrange multipliers, obtained here without them.
--
--   **Formalization Note** Differentiability is Fréchet differentiability of the real value of $F$ (finite near an inner point of $A_R$) at $a$, with derivative the linear map $b\mapsto\sum_i t_i b_i$. The statement is made for every $(Q, c, t)$ satisfying the hypotheses; its existence is Theorem 3.3. The density equation holds $R$-almost everywhere.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 158 (PDF 13), Remark

import Mathlib
import Definitions.Def_IDivGeom_ExpFam_Setting

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.ExpFam

theorem remark_grad_F {X : Type*} [MeasurableSpace X]
    (k : ℕ) (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i))
    (R : Measure X) [IsProbabilityMeasure R] (hT : IsOpen (expIntegrableSet f R)) :
    ∀ a ∈ interior (finiteSet f R), ∀ (Q : Measure X) (c : ℝ) (t : Fin k → ℝ),
      IDivGeom.IPFP.IsIProjection R (IDivGeom.IPFP.momentSet f a) Q →
      (∀ᵐ x ∂ R, (Q.rnDeriv R x).toReal = c * Real.exp (∑ i, t i * f i x)) →
      HasFDerivAt (fun b => (valueFn f R b).toReal)
        (∑ i, t i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i) a := by sorry

end IDivGeom.ExpFam
