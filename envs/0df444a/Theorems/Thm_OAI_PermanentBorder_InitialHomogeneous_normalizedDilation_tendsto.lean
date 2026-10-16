-- Prove2me | Theorems.Thm_OAI_PermanentBorder_InitialHomogeneous_normalizedDilation_tendsto
-- name    : OAI.PermanentBorder.InitialHomogeneous.normalizedDilation_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:18:09.633902+00:00
-- url     : https://prove2.me/theorems/80cc62e0-8e9b-4201-b29a-ee8f0e113f69
-- title:
--   Normalized dilations $t^{-r}q(tx)$ converge coefficientwise to the degree-$r$ homogeneous component as $t\to 0$
-- statement:
--   Let $\sigma$ be a finite set, $x=(x_v)_{v\in\sigma}$, and let $q\in\mathbb{C}[x]$ be a complex polynomial. For an exponent vector $e\in\mathbb{N}^{\sigma}$ let $|e|=\sum_{v\in\sigma}e_v$ be its total degree and $[x^e]q$ the coefficient of $x^e=\prod_v x_v^{e_v}$ in $q$. For $k\in\mathbb{N}$ the homogeneous component $q_k$ of degree $k$ is the sum of the terms of $q$ of total degree $k$, so $[x^e]q_k=[x^e]q$ if $|e|=k$ and $[x^e]q_k=0$ otherwise. For $r\in\mathbb{N}$ and $t\in\mathbb{C}\setminus\{0\}$, the *normalized dilation* of $q$ is the polynomial $t^{-r}q(tx)$, where $q(tx)$ denotes the result of substituting $x_v\mapsto t\,x_v$ for every $v\in\sigma$.
--
--   **Theorem.** Let $r\in\mathbb{N}$ and suppose $q_k=0$ for every $k<r$. Let $\mathcal{L}$ be a filter on a set $I$ and let $t:I\to\mathbb{C}$ satisfy $t(i)\to0$ along $\mathcal{L}$ and $t(i)\neq0$ for $\mathcal{L}$-eventually all $i$. Then for every exponent vector $e\in\mathbb{N}^{\sigma}$,
--
--   $$
--   \lim_{i\to\mathcal{L}}\ [x^e]\Bigl(t(i)^{-r}\,q\bigl(t(i)\,x\bigr)\Bigr)=[x^e]\,q_r .
--   $$
--
--   Typical instances are a sequence $t_j\to0$ of nonzero complex numbers (the filter $\mathcal{L}$ being "$j\to\infty$" on $\mathbb{N}$) and a real parameter $t\to0^+$.
--
--   The theorem says that the rescalings $t^{-r}q(tx)$ degenerate, coefficient by coefficient, to the homogeneous component $q_r$; when $q_r\neq0$ this is the lowest-degree part (initial form) of $q$ at the origin. It is the limiting input for showing that properties preserved by linear substitutions, scalar multiples and coefficientwise limits, such as having a border determinant of a given size, pass from $q$ to its initial form.
--
--   **Formalization Note** The normalized dilation is `normalizedDilation r q t = (t ^ r)⁻¹ • dilation t q`, where `dilation t` is the substitution `x v ↦ t * x v`, written as an affine substitution with zero translation. Lean's convention `0⁻¹ = 0` makes the expression at `t = 0` a junk value, which is why the statement assumes `∀ᶠ i in l, t i ≠ 0`. The vanishing of the lower components is the hypothesis `∀ j < r, homogeneousComponent j q = 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/InitialForm.lean#L67-L90

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model
import Definitions.Def_OAI_Algebra_Determinantal_BorderPolars
import Definitions.Def_OAI_Algebra_Determinantal_InitialForm

open OAI OAI.PermanentBorder OAI.PermanentBorder.InitialHomogeneous
open MvPolynomial Filter
open scoped Topology
variable {σ : Type*} [Fintype σ]

theorem OAI.PermanentBorder.InitialHomogeneous.normalizedDilation_tendsto {α : Type*} {l : Filter α}
    {q : Poly σ} {r : ℕ}
    (hlow : ∀ j < r, homogeneousComponent j q = 0)
    {t : α → ℂ} (ht : Tendsto t l (𝓝 0))
    (hne : ∀ᶠ j in l, t j ≠ 0) (e : σ →₀ ℕ) :
    Tendsto (fun j => (normalizedDilation r q (t j)).coeff e)
      l (𝓝 ((homogeneousComponent r q).coeff e)) := by sorry
