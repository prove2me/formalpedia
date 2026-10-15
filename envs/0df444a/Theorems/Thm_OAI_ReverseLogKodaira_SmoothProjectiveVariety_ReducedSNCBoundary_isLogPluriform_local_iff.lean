-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_ReducedSNCBoundary_isLogPluriform_local_iff
-- name    : OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.isLogPluriform_local_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:52:31.805842+00:00
-- url     : https://prove2.me/theorems/072a9213-6417-4396-9714-a9ae1bcd80cd
-- title:
--   Logarithmic pluricanonical forms can be detected on one boundary chart around each point
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field. For a smooth projective variety $X$, write $\omega^m_{K(X)}=\big(\textstyle\bigwedge^{\dim X}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m}$ for the one-dimensional $K(X)$-vector space of rational $m$-pluricanonical forms. For a nonempty affine open $W\subseteq X$, the *regular lattice* $L_m(W)\subseteq\omega^m_{K(X)}$ is the $\mathcal{O}_X(W)$-submodule spanned by all forms $\bigotimes_{j=1}^{m}\big(da_{j,1}\wedge\cdots\wedge da_{j,\dim X}\big)$ with $a_{j,i}\in\mathcal{O}_X(W)$ (viewed in $K(X)$).
--
--   A *reduced simple normal crossing (SNC) boundary* $E$ on a smooth projective variety $X$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim X-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_X(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$. A form $s\in\omega^m_{K(X)}$ is a *log $m$-pluriform* for $(X,E)$ if $t^m s\in L_m(W)$ for every nonempty affine open $W$ and every nonzero $t\in\mathcal{O}_X(W)$ with $\mathcal{I}_E(W)=(t)$; these forms make up a $\mathbb{C}$-subspace $S_m(X,E)\subseteq\omega^m_{K(X)}$, the formal counterpart of $H^0\big(X,m(K_X+E)\big)$.
--
--   Let $E$ be a reduced SNC boundary on a smooth projective variety $X$. For every $m\in\mathbb{N}$ and every $s\in\omega^m_{K(X)}$, the form $s$ is a log $m$-pluriform for $(X,E)$ if and only if
--   $$
--   \forall x\in X\ \ \exists\,W\ni x\ \text{nonempty affine open},\ \exists\,t\in\mathcal{O}_X(W)\setminus\{0\}:\quad \mathcal{I}_E(W)=(t)\ \text{ and }\ t^m s\in L_m(W).
--   $$
--   Here $x$ ranges over all points of the scheme $X$.
--
--   The definition of a log pluriform quantifies over all affine charts and all local equations of the boundary; this criterion shows that it suffices to exhibit, around each point, a single chart with a single local equation. It is the tool used to verify that a form constructed chart by chart, such as the restriction of a log pluricanonical form to a fibre, has logarithmic poles.
--
--   **Formalization Note** The left-hand side is `E.IsLogPluriform m s`, the boundary ideal is `E.ideal`, and $t^m$ acts on `X.RationalPluriform m` through the image of $t$ in the function field.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/LogLattice.lean#L180-L232

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.isLogPluriform_local_iff {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) (m : ℕ) (s : X.RationalPluriform m) :
    E.IsLogPluriform m s ↔
      ∀ x : X.scheme, ∃ (U : X.scheme.affineOpens) (hU : Nonempty U.1), x ∈ U.1 ∧
        ∃ t : Γ(X.scheme, U.1), t ≠ 0 ∧ E.ideal.ideal U = Ideal.span {t} ∧
          (algebraMap Γ(X.scheme, U.1) X.scheme.functionField t)^m • s ∈
            @regularPluriformLattice X U hU m := by sorry
