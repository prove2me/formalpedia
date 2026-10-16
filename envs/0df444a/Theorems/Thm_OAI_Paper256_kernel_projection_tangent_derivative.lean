-- Prove2me | Theorems.Thm_OAI_Paper256_kernel_projection_tangent_derivative
-- name    : OAI.Paper256.kernel_projection_tangent_derivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:40:15.791224+00:00
-- url     : https://prove2.me/theorems/f67ce4f2-6363-4a84-8f2b-62be1b01b358
-- title:
--   Kernel projections of $E(I-uu^{\mathsf T})$ are differentiable along tangent curves on the sphere, linearly in the direction
-- statement:
--   Let $c\ge1$, let $\mathrm{Sym}_k$ denote the real symmetric $k\times k$ matrices, and let $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$ be a real-linear map. For $M\in\mathbb{R}^{c\times c}$ let $K(M)$ be the matrix of the orthogonal projection of $\mathbb{R}^c$ (standard inner product) onto $\ker M$. Vectors $u\in\mathbb{R}^4$ have coordinates $u_0,\dots,u_3$, Euclidean norm $\|u\|$ and inner product $\langle\cdot,\cdot\rangle$. For $v,h\in\mathbb{R}^4$ define the curve
--   $$
--   \gamma_{v,h}(s)=\frac{v+sh}{\sqrt{1+s^2\|h\|^2}},\qquad s\in\mathbb{R};
--   $$
--   when $\|v\|=1$ and $\langle v,h\rangle=0$ it lies on the unit sphere and passes through $v$ at $s=0$ with velocity $h$.
--
--   **Theorem.** There exist a unit vector $v\in\mathbb{R}^4$ with $v_0\neq0$ and a linear map $T:\mathbb{R}^4\to\mathbb{R}^{c\times c}$ such that for every $h\in\mathbb{R}^4$ with $\langle v,h\rangle=0$ the function $s\mapsto K\big(E(I_4-\gamma_{v,h}(s)\gamma_{v,h}(s)^{\mathsf T})\big)$ is differentiable at $s=0$ with
--   $$
--   \frac{d}{ds}\Big|_{s=0}K\Big(E\big(I_4-\gamma_{v,h}(s)\,\gamma_{v,h}(s)^{\mathsf T}\big)\Big)=T(h).
--   $$
--
--   So, at a suitable point $v$ of the sphere, the kernel projections of $E(I_4-uu^{\mathsf T})$ have a first-order expansion along every tangent direction $h$, with a derivative that depends linearly on $h$. This is used in a tangent-space argument concerning linear matrix inequality representations of a hyperbolicity cone.
--
--   **Formalization Note** $\gamma_{v,h}$ is `tangentCurve v h`, $uu^{\mathsf T}$ is `outerSym u`, $K$ is `kernelProjection`, and $\mathbb{R}^4$ is `Vec 4 = EuclideanSpace ℝ (Fin 4)`. Differentiability is `HasDerivAt … (T h) 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/KernelTangent.lean#L13-L34

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

open OAI OAI.Paper256
open scoped ContDiff Topology RealInnerProductSpace Matrix.Norms.L2Operator
open Set Filter

theorem OAI.Paper256.kernel_projection_tangent_derivative (c : ℕ) (hC : 0 < c)
    (E : Sym 4 →ₗ[ℝ] Sym c) :
    ∃ (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat c ℝ),
      ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ ∀ h : Vec 4, inner ℝ v h = 0 →
        HasDerivAt (fun s : ℝ => kernelProjection
          (E (1 - outerSym (tangentCurve v h s)) : Mat c ℝ)) (T h) 0 := by sorry
