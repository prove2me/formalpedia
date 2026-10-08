-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_lemma2_lipschitz
-- name    : NesterovRCD.Sublinear.lemma2_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:59.506842+00:00
-- url     : https://prove2.me/theorems/b8a7b0cd-1db9-4460-8e99-a6e84505f680
-- title:
--   Lemma 2, (2.9) — $\|\nabla f(x)-\nabla f(y)\|^*_{1-\alpha}\le S_\alpha\|x-y\|_{1-\alpha}$
-- statement:
--   Let $f:\mathbb R^N\to\mathbb R$ be convex and satisfy (2.2) with constants $L_i>0$, and let $\alpha\in\mathbb R$. With $S_\alpha=\sum_{i=1}^nL_i^\alpha$ and the norms (2.7),
--   $$\|\nabla f(x)-\nabla f(y)\|^*_{1-\alpha}\le S_\alpha\|x-y\|_{1-\alpha}\qquad\text{for all }x,y\in\mathbb R^N .$$
--
--   The lemma links the coordinate-wise condition (2.2) with a full-dimensional Lipschitz condition on the gradient in the weighted norm $\|\cdot\|_{1-\alpha}$.
--
--   **Formalization Note** The paper states the lemma under (2.2) alone; convexity of $f$ is the standing assumption of §2 (p. 4) and its proof uses it (it applies (2.4) to $f-f^*$ and to $x\mapsto f(x)-f(y)-\langle\nabla f(y),x-y\rangle$, which is minimized at $y$ only for convex $f$). We state convexity explicitly. Without it the claim is false: $f(x)=x_1x_2$ on $\mathbb R^2$ satisfies (2.2) with $L_1=L_2=\varepsilon$ for every $\varepsilon>0$. The gradient difference is written block by block, $(f'_i(x)-f'_i(y))_i$. All real $\alpha$ are allowed, as in the lemma.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 6, Lemma 2, (2.9)

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic

namespace NesterovRCD.Sublinear

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem lemma2_lipschitz (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L) (α : ℝ) (x y : Blocks E) :
    wdual L (1 - α) (fun i => partialGrad f x i - partialGrad f y i)
      ≤ S L α * wnorm L (1 - α) (x - y) := by sorry

end NesterovRCD.Sublinear
