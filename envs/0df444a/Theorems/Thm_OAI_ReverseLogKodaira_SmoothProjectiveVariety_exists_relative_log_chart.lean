-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_exists_relative_log_chart
-- name    : OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_relative_log_chart
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:10:48.442912+00:00
-- url     : https://prove2.me/theorems/f23da5ad-dcdd-4ebb-b7ae-83063c5df8e7
-- title:
--   Relative log charts: standard smooth affine charts of relative dimension $\dim X-\dim Y$ carrying a local boundary equation
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field and $\mathcal{O}_Z(W)$ the ring of sections over an open set $W$. A *reduced simple normal crossing (SNC) boundary* $E$ on $Z$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim Z-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_Z(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$.
--
--   Let $(X,E)$ and $(Y,D)$ be smooth projective varieties with reduced SNC boundaries, and let $f\colon(X,E)\to(Y,D)$ be a *stratum-smooth fibration*: $f\colon X\to Y$ is a surjective morphism over $\mathbb{C}$ whose fibres $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$ over all complex points $y$ are connected, with $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$, such that over $Y^{\circ}:=Y\setminus\operatorname{Supp}D$ both $f$ and its restriction to every stratum of $E$ (the closed subscheme cut out by $\sum_{i\in S}\mathcal{I}_{E_i}$, for each nonempty set $S$ of components) are smooth. A ring homomorphism $R\to S$ is *standard smooth of relative dimension $d$* if $S\cong R[x_1,\dots,x_N]/(g_1,\dots,g_k)$ with $N-k=d$ and, after renumbering the variables, the Jacobian determinant $\det\big(\partial g_i/\partial x_j\big)_{1\le i,j\le k}$ is a unit in $S$.
--
--   Let $f\colon(X,E)\to(Y,D)$ be a stratum-smooth fibration, let $U\subseteq Y$ be an affine open contained in $Y^{\circ}=Y\setminus\operatorname{Supp}D$, let $O\subseteq X$ be an open set and let $x\in O$ be a point of the scheme $X$ with $f(x)\in U$. Then there exist an affine open $V\subseteq X$ and an element $t\in\mathcal{O}_X(V)$ such that
--
--   $$
--   x\in V\subseteq O,\qquad V\subseteq f^{-1}(U),\qquad t\neq0,\qquad \mathcal{I}_E(V)=(t),
--   $$
--
--   and the ring homomorphism $f^{*}\colon\mathcal{O}_Y(U)\to\mathcal{O}_X(V)$ is standard smooth of relative dimension $\dim X-\dim Y$.
--
--   Such a *relative log chart* is adapted both to the fibration, since $\mathcal{O}_X(V)$ is a standard smooth algebra over the base chart, and to the boundary, since $t$ is a local equation of $E$. These charts can be found inside any neighbourhood of any point lying over $U$. On them, logarithmic pluricanonical forms on $X$ are written as a numerator divided by $t^m$ and then restricted to the fibres of $f$.
--
--   **Formalization Note** $Y^{\circ}$ is `D.complement`, and the ring map is `f.hom.appLE U V e`. The number $\dim X-\dim Y$ is natural-number subtraction of the dimensions recorded in the structures. The hypotheses force $\dim Y\le\dim X$, because $f^{-1}(Y^{\circ})$ contains $x$ and is therefore nonempty, so this is the usual difference.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean#L200-L245

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_relative_log_chart
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (O : X.scheme.Opens) (x : X.scheme) (hx : x ∈ O) (hfx : f.hom x ∈ U.1) :
    ∃ (V : X.scheme.affineOpens), x ∈ V.1 ∧ V.1 ≤ O ∧
      ∃ (e : V.1 ≤ f.hom ⁻¹ᵁ U.1),
        RingHom.IsStandardSmoothOfRelativeDimension (X.dimension - Y.dimension)
          (f.hom.appLE U.1 V.1 e).hom ∧
        ∃ t : Γ(X.scheme, V.1), t ≠ 0 ∧ E.ideal.ideal V = Ideal.span {t} := by sorry
