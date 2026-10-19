-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_mul_mem_lowDegree
-- name    : OAI.MatchingSmoothing.mul_mem_lowDegree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:28:31.194005+00:00
-- url     : https://prove2.me/theorems/3d4afa62-dca3-4b64-a068-c3ed8279df94
-- title:
--   Products of low-degree polynomial functions: degrees add
-- statement:
--   Let $E$ and $X$ be arbitrary sets and let $x=(x_e)_{e\in E}$ be a family of real-valued functions $x_e:X\to\mathbb R$, regarded as coordinate functions on $X$. For $d\in\mathbb N$ let
--
--   $$
--   \mathcal L_d(x)=\operatorname{span}_{\mathbb R}\big\{\,x_{e_1}x_{e_2}\cdots x_{e_\ell}\;:\;0\le\ell\le d,\ e_1,\dots,e_\ell\in E\,\big\}\subseteq\mathbb R^X
--   $$
--
--   be the space of functions on $X$ that are polynomials of degree at most $d$ in the coordinates. Products are pointwise, the indices $e_1,\dots,e_\ell$ may repeat, and the empty product ($\ell=0$) is the constant function $1$.
--
--   Then for all $d,e\in\mathbb N$ and all functions $f,g:X\to\mathbb R$,
--
--   $$
--   f\in\mathcal L_d(x)\ \text{ and }\ g\in\mathcal L_e(x)\quad\Longrightarrow\quad f\,g\in\mathcal L_{d+e}(x).
--   $$
--
--   So the spaces $\mathcal L_0(x)\subseteq\mathcal L_1(x)\subseteq\cdots$ form a filtration of the algebra of real functions on $X$ that is compatible with multiplication. With this, a product of $s$ functions, each of degree at most $1$, has degree at most $s$. For example, an indicator of a $0/1$ pattern $\prod_{e\in A}x_e\prod_{e\in B}(1-x_e)$ has degree at most $|A|+|B|$. In the matching setting, $X$ is a set of perfect matchings and $x_e$ is the indicator that the edge $e$ is present.
--
--   **Formalization Note** $\mathcal L_d(x)$ is `lowDegree x d`, the span of the products `(l.map x).prod` over lists `l` of indices of length at most `d`. Nothing is assumed about the sizes of $E$ and $X$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/EdgeProducts.lean#L26-L43

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4
variable {E : Type u_1} {X : Type u_2}

theorem OAI.MatchingSmoothing.mul_mem_lowDegree (x : E → X → ℝ) {d e : ℕ} {f g : X → ℝ}
    (hf : f ∈ lowDegree x d) (hg : g ∈ lowDegree x e) :
    f * g ∈ lowDegree x (d + e) := by sorry
