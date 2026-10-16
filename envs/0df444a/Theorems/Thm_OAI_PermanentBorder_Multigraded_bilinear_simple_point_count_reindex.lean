-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Multigraded_bilinear_simple_point_count_reindex
-- name    : OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_reindex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:32:08.350209+00:00
-- url     : https://prove2.me/theorems/ebcaec37-2e6e-4850-9e89-e12b4c56864c
-- title:
--   Multihomogeneous Bézout bound for simple zeros of a square block-bilinear system, for arbitrary index sets
-- statement:
--   Let $\iota$ be a finite set of *blocks* and let $a=(a_j)_{j\in\iota}$ be natural numbers. Let $\sigma$ be a finite set of variables with a block map $g:\sigma\to\iota$, together with a bijection between $\sigma$ and $\bigsqcup_{j\in\iota}\{0,1,\dots,a_j\}$ that sends every variable of block $j$ into the $j$-th summand. Thus block $j$ consists of exactly $a_j+1$ variables, which serve as homogeneous coordinates on $\mathbb{P}^{a_j}$, and $\mathbb{C}^{\sigma}$ is the space of homogeneous coordinates of $\prod_{j\in\iota}\mathbb{P}^{a_j}$. A polynomial in $\mathbb{C}[x_s:s\in\sigma]$ has *multidegree* $\delta\in\mathbb{Z}^{\iota}$ if every monomial occurring in it has total degree $\delta_j$ in the variables of block $j$, for every $j$. Write $\mathbf{e}_j$ for the $j$-th unit vector of $\mathbb{Z}^{\iota}$.
--
--   Let $E$ be a finite set of equations with $|E|=\sum_{j\in\iota}a_j$, let $u,v:E\to\iota$, and let $F_i\in\mathbb{C}[x_s:s\in\sigma]$ ($i\in E$) have multidegree $\mathbf{e}_{u(i)}+\mathbf{e}_{v(i)}$; so $F_i$ is bilinear in the blocks $u(i)$ and $v(i)$, or quadratic in block $u(i)$ if $u(i)=v(i)$. Let $V$ be a complex Banach space and $\Lambda$ a finite set, and suppose that for every $\lambda\in\Lambda$ we are given
--
--   - a continuous linear isomorphism $\varepsilon_\lambda:\mathbb{C}^{E}\to V$;
--   - a complex continuously differentiable map $\phi_\lambda:V\to\mathbb{C}^{\sigma}$ and, for each block $j$, a variable $b_\lambda(j)\in\sigma$ of block $j$ such that $\phi_\lambda(z)_{b_\lambda(j)}=1$ for all $z\in V$ (so $\phi_\lambda$ is a chart into an affine piece of the multiprojective space);
--   - a point $x_\lambda\in V$ such that $p_\lambda:=\phi_\lambda(x_\lambda)$ satisfies $F_i(p_\lambda)=0$ for all $i\in E$, and such that the map $\Phi_\lambda:V\to V$, $\Phi_\lambda(z)=\varepsilon_\lambda\big((F_i(\phi_\lambda(z)))_{i\in E}\big)$, has invertible derivative $D\Phi_\lambda(x_\lambda)$.
--
--   Assume moreover that for $\lambda\neq\mu$ the points $p_\lambda$ and $p_\mu$ are *block separated*: there are variables $s,t$ in the same block with $p_\lambda(s)\,p_\mu(t)\neq p_\lambda(t)\,p_\mu(s)$, i.e. they define different points of $\prod_j\mathbb{P}^{a_j}$. Then
--
--   $$
--   |\Lambda|\;\le\;\big[T^{a}\big]\prod_{i\in E}\big(T_{u(i)}+T_{v(i)}\big),
--   $$
--
--   the coefficient of the monomial $T^{a}=\prod_{j\in\iota}T_j^{a_j}$ in the displayed polynomial with natural-number coefficients in formal variables $(T_j)_{j\in\iota}$.
--
--   This is the multihomogeneous Bézout bound for nondegenerate common zeros of a square system of block-bilinear equations, with the zeros described in local affine charts. This version allows arbitrary finite index sets for the variables and the equations, which is the form needed when it is applied to the kernel system of a determinantal matrix pencil.
--
--   **Formalization Note** The multidegree condition is `IsWeightedHomogeneous (blockWeight group)`, where each variable $s$ has weight $\mathbf{e}_{g(s)}$; the bijection is `ve : σ ≃ BlockVariables a`, with `BlockVariables a` the sigma type of the `Fin (a j + 1)`; $a$ is a finitely supported function `ι →₀ ℕ`; the right-hand side is `(mixedPolynomial u v).coeff a` in `MvPolynomial ι ℕ`; invertibility is `ContinuousLinearMap.IsInvertible` of `fderiv ℂ`; the points are indexed by the finite type `L` (our $\Lambda$), and each chart is required to be $C^1$ on all of $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/KernelCharts.lean#L34-L92

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts

open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_reindex (a : ι →₀ ℕ)
    (group : σ → ι) (ve : σ ≃ BlockVariables a)
    (hv : ∀ s, (ve s).1 = group s)
    (u v : E → ι) (hM : Fintype.card E = ∑ j, a j)
    (F : E → MvPolynomial σ ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (blockWeight group)
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (base : L → ι → σ) (hbase : ∀ i j, group (base i j) = j)
    (e : L → (E → ℂ) ≃L[ℂ] V)
    (chart : L → V → σ → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated group (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by sorry
