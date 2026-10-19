-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Weighted_block_reconstruct
-- name    : OAI.SubsphereCurrent.Weighted.block_reconstruct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:59:39.684315+00:00
-- url     : https://prove2.me/theorems/67a26039-1248-4d2a-9576-4625cc330cf1
-- title:
--   Gaussian splitting identity for the radius-weighted affine average of a block input
-- statement:
--   Let $d,n,m\in\mathbb N$ and let $A$ be an *affine test* of dimension $n$ in $\mathbb R^d$: a linear subspace $H\subseteq\mathbb R^d$ with $\dim H=n$, a center $c\in H^\perp$ and a radius $r>0$ with $\|c\|^2+r^2=1$; assume $H\ne\{0\}$. For $s$ in the unit sphere $S_H$ of $H$, the point $c+rs$ lies on the unit sphere $S^{d-1}$ of $\mathbb R^d$. Write $\sigma_H$ for the uniform (normalized surface) measure on $S_H$ and $\gamma_F$ for the standard Gaussian measure on a Euclidean space $F$.
--
--   Let $V$ be a finite index set and, for $v\in V$, let $\kappa_v:(\mathbb R^d)^m\times\mathbb R^m\to[0,\infty]$ and $g_v:S^{d-1}\to[0,\infty]$ be measurable. Define:
--
--   1. the *block input* $\displaystyle \beta(s)=\int_{(\mathbb R^d)^m}\sum_{v\in V}\kappa_v\big(X,(\langle X_i,s\rangle)_{i\le m}\big)\,g_v(s)\,d\gamma_{\mathbb R^d}^{\otimes m}(X)$ for $s\in S^{d-1}$;
--   2. the *weighted restriction* $g^A(s)=r^{d/16}\,g(c+rs)$ for $g:S^{d-1}\to[0,\infty]$ and $s\in S_H$;
--   3. the *pulled-back observation* $\Phi_w(X,y)=\big((X_i+w_i)_{i\le m},\,(\langle X_i+w_i,c\rangle+r\,y_i)_{i\le m}\big)$ for $w=(w_1,\dots,w_m)\in(H^\perp)^m$, $X\in H^m$ and $y\in\mathbb R^m$.
--
--   **Theorem.** With these notations,
--
--   $$
--   r^{d/16}\int_{S_H}\beta(c+rs)\,d\sigma_H(s)=\int_{(H^\perp)^m}\sum_{v\in V}\int_{S_H}g_v^A(s)\left(\int_{H^m}\kappa_v\Big(\Phi_w\big(X,(\langle s,X_i\rangle)_{i\le m}\big)\Big)\,d\gamma_H^{\otimes m}(X)\right)d\sigma_H(s)\,d\gamma_{H^\perp}^{\otimes m}(w).
--   $$
--
--   The left side is the quantity whose supremum over affine tests of dimension $n$ defines the radius-weighted norm of the block input. The identity rewrites it exactly as an average, over the components $w$ of the Gaussian rows orthogonal to $H$, of a routing expression that lives entirely in the $n$-dimensional space $H$: the kernels $\kappa_v\circ\Phi_w$ are applied to Gaussian rows in $H$ and their labels against $s\in S_H$, with weights $g_v^A$ on $S_H$. This is what allows a routing bound on the sphere $S_H$ to be applied for each fixed $w$ when estimating the weighted norm of a block input.
--
--   **Formalization Note** The exponent $d/16$ is the real number $d/16$ (not an integer part). Both sides are lower Lebesgue integrals of $[0,\infty]$-valued functions; $\beta$, $g^A$ and $\Phi_w$ are `blockInput κ g`, `weightedOnTest A g` and `pullObservation A w`, and $s\mapsto c+rs$ is `onTest A`. The instance that $H$ is nontrivial is part of the statement's context.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Affine.lean#L630-L701

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Weighted
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {d n m : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
variable {V : Type*} [Fintype V]

theorem OAI.SubsphereCurrent.Weighted.block_reconstruct (κ : V → Observation d m → ℝ≥0∞) (hκ : ∀ v, Measurable (κ v))
    (g : V → Sphere d → ℝ≥0∞) (hg : ∀ v, Measurable (g v)) :
    (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
      (∫⁻ s, blockInput κ g (onTest A s) ∂Affine.sphereLaw A.space) =
    ∫⁻ w : Fin m → A.spaceᗮ,
      (∑ v, ∫⁻ s : Affine.Sphere A.space, weightedOnTest A (g v) s *
        (∫⁻ X : Fin m → A.space, κ v (pullObservation A w (X,fun i => ⟪s.val,X i⟫))
          ∂Measure.pi (fun _ => stdGaussian A.space)) ∂Affine.sphereLaw A.space)
      ∂Measure.pi (fun _ => stdGaussian A.spaceᗮ) := by sorry
