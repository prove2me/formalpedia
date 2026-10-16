-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Cometric_uniform_cometric_bounds
-- name    : OAI.ThreeManifold.Cometric.uniform_cometric_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:26:12.388709+00:00
-- url     : https://prove2.me/theorems/083644a6-64bf-49d9-af3f-61aadda0c8a8
-- title:
--   Uniform ellipticity, derivative and concavity bounds for the two neck cometrics
-- statement:
--   Let $a(u)=e^{-1/(2/3-u)}$ for $u<2/3$ and $a(u)=0$ for $u\ge 2/3$; this is a smooth function with values in $[0,1)$. Let $\mathcal{A}(u)=\int_0^u a(y)\,dy$, and let $\chi(t)=\psi\bigl(6(t-5/12)\bigr)$, where $\psi$ is the standard smooth transition function ($C^\infty$, nondecreasing, $\psi=0$ on $(-\infty,0]$ and $\psi=1$ on $[1,\infty)$). So $\chi$ rises from $0$ to $1$ on $[5/12,7/12]$. For parameters $\delta,t\in\mathbb{R}$ put
--   $$
--   d_1=1+\delta\mathcal{A}(t),\qquad d_2=1+\delta\mathcal{A}(1-t),\qquad s=\delta^2\chi(t),\qquad
--   P(\delta,t)=\begin{pmatrix}d_1+d_2s^2 & d_2s\\ d_2s & d_2\end{pmatrix}.
--   $$
--
--   Let $C_2(\delta)=\begin{pmatrix}0&1\\1&-\delta^2\end{pmatrix}$ and $P^{\mathrm{end}}(\delta,\tau)=C_2(\delta)\,P(\delta,1-\tau)\,C_2(\delta)^{\mathsf T}$. The *coordinate cometric* on side $\varepsilon\in\{\text{left},\text{right}\}$ is $R^{\delta}_{\text{left}}(t)=P(\delta,t)$ and $R^{\delta}_{\text{right}}(t)=P^{\mathrm{end}}(\delta,t)$. Write $|p|^2=p_0^2+p_1^2$ and $q_M(p)=p^{\mathsf T}Mp$, and let primes denote derivatives in $t$.
--
--   **Theorem.** There exist constants $\delta_0$ and $C$ with $0<\delta_0\le1/2$ and $C>0$ such that for every $\delta\in(0,\delta_0]$, each side $\varepsilon$, every $t\in[0,1]$ and every $p\in\mathbb{R}^2$, writing $R=R^\delta_\varepsilon$:
--
--   1. $\dfrac{|p|^2}{9}\le q_{R(t)}(p)\le 18\,|p|^2$;
--   2. $\dfrac{|p|^2}{18}\le q_{R(t)^{-1}}(p)\le 9\,|p|^2$;
--   3. $|R'(t)\,p|^2\le C^2\delta^2\,|p|^2$;
--   4. $0\le q_{-R''(t)}(p)$;
--   5. $|R'(t)\,p|^2\le C\,\delta\;q_{-R''(t)}(p)$.
--
--   In display form, the last two say that
--   $$
--   -R''(t)\succeq 0\qquad\text{and}\qquad |R'(t)p|^2\le C\delta\,\bigl(-p^{\mathsf T}R''(t)p\bigr).
--   $$
--
--   These are the uniform estimates on the cometrics of the two neck regions used in the construction: uniformly elliptic, $C^1$-close to constant at rate $\delta$, concave, and with the square of the first derivative dominated by $\delta$ times the concavity. The right cometric is the left one reflected in $t$ and transported by the linear change of torus coordinates $C_2(\delta)$.
--
--   **Formalization Note** $R'$ and $R''$ are Lean's `deriv` and `deriv (deriv ·)` of the matrix-valued function; $R$ is smooth, so these are the true derivatives. $R(t)^{-1}$ is Lean's matrix inverse, which is the genuine inverse here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L1451-L1483

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Matrix
open scoped Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Cometric.uniform_cometric_bounds : ∃ δ₀ C : ℝ,
    0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ 0 < C ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀, ∀ right : Bool, ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : V2,
      let R := coordinateCometric right δ
      (sqnorm p / 9 ≤ qform (R t) p ∧ qform (R t) p ≤ 18 * sqnorm p) ∧
      (sqnorm p / 18 ≤ qform (R t)⁻¹ p ∧ qform (R t)⁻¹ p ≤ 9 * sqnorm p) ∧
      sqnorm (deriv R t *ᵥ p) ≤ C ^ 2 * δ ^ 2 * sqnorm p ∧
      0 ≤ qform (-deriv (deriv R) t) p ∧
      sqnorm (deriv R t *ᵥ p) ≤ C * δ * qform (-deriv (deriv R) t) p := by sorry
