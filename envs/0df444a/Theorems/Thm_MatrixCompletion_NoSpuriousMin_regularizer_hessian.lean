-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_regularizer_hessian
-- name    : MatrixCompletion.NoSpuriousMin.regularizer_hessian
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-13T23:57:45.515691+00:00
-- url     : https://prove2.me/theorems/8bf5e952-5124-4fd3-9fd9-34e611d3491d
-- title:
--   Hessian of the regularizer: $\frac{d}{ds}\langle\nabla R(X+sV),V\rangle|_{0}=\langle V,\nabla^2R(X)[V]\rangle$
-- statement:
--   Let $R(X)=\sum_{i=1}^{d}(\|X_i\|-\alpha)_+^4$ be the row regularizer with threshold $\alpha>0$. Its gradient is $\nabla R(X)=\Gamma X$ (the companion milestone), so the directional derivative of $R$ at a point $Y$ along $V$ is $\langle\nabla R(Y),V\rangle$. This statement is the second-order half of the same calculus: as the base point slides along the direction $V$, that directional derivative is itself differentiable at $s=0$, with
--
--   $$\frac{d}{ds}\Big\langle \nabla R(X+sV),\,V\Big\rangle\bigg|_{s=0} \;=\; \big\langle V,\ \nabla^2 R(X)[V]\big\rangle .$$
--
--   Equivalently, $s\mapsto R(X+sV)$ is twice differentiable at $0$ and its second derivative is the Hessian quadratic form $\mathrm{vec}(V)^\top\nabla^2R(X)\,\mathrm{vec}(V)$. Row by row, for the radial function $x\mapsto h(\|x\|)$ with $h(t)=(t-\alpha)_+^4$, the Hessian is
--
--   $$h''(t)\,uu^\top+\frac{h'(t)}{t}\left(I-uu^\top\right),\qquad t=\|X_i\|,\quad u=X_i/t,$$
--
--   with $h'(t)=4(t-\alpha)_+^3$ and $h''(t)=12(t-\alpha)_+^2$, which is exactly the quantity the mission's model layer records.
--
--   **Formalization Note** The statement is phrased as a directional derivative of the directional gradient, mirroring the gradient milestone, so that no norm has to be fixed on matrix space and no second-order Frechet machinery is needed. The hypothesis $\alpha>0$ is what makes the formula correct at rows with $X_i=0$: there $R$ vanishes identically in a neighbourhood, and the formula's $0/0$ terms are $0$ under Lean's division convention, so both sides are zero. This is the missing analytic input to the first- and second-order optimality conditions (Chen-Li Lemma 4.3): the smooth part of the objective is a quartic polynomial along any line, so the regularizer is the only term whose second derivative needs an argument.
-- source:
--   Ge, Lee, Ma 2016, Matrix Completion has No Spurious Local Minimum, https://arxiv.org/abs/1605.07272 (v4), p. 11, Proposition 5.2 (the Hessian half; the printed exponent 4 in the gradient is corrected to 3 per the derivative of (t-alpha)_+^4 and the rank-1 form on its p. 9). Explicit Hessian form: Ge, Jin, Zheng 2017, No Spurious Local Minima in Nonconvex Low Rank Problems, https://arxiv.org/abs/1704.00708, Lemma 18. Used by: Chen, Li 2019, Model-free Nonconvex Matrix Completion, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3), pp. 16-19, Lemma 4.3 (second-order optimality condition).

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Analysis.Calculus.Deriv.Basic
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.regularizer_hessian
    {d r : ℕ} (α : ℝ) (hα : 0 < α) (X V : Matrix (Fin d) (Fin r) ℝ) :
    HasDerivAt (fun s : ℝ => innerM (regGrad α (X + s • V)) V) (regHessQF α X V) 0 := by sorry
