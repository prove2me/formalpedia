-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_local_logarithmic_numerator
-- name    : OAI.ReverseLogKodaira.FiberChartSpecialization.local_logarithmic_numerator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:55:57.062105+00:00
-- url     : https://prove2.me/theorems/4f1b1c9b-3ce1-4df9-a68a-52618eebdc37
-- title:
--   A log pluricanonical form is a regular form divided by the $m$-th power of a local boundary equation
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field. For a smooth projective variety $X$, write $\omega^m_{K(X)}=\big(\textstyle\bigwedge^{\dim X}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m}$ for the one-dimensional $K(X)$-vector space of rational $m$-pluricanonical forms. For a nonempty affine open $W\subseteq X$, the *regular lattice* $L_m(W)\subseteq\omega^m_{K(X)}$ is the $\mathcal{O}_X(W)$-submodule spanned by all forms $\bigotimes_{j=1}^{m}\big(da_{j,1}\wedge\cdots\wedge da_{j,\dim X}\big)$ with $a_{j,i}\in\mathcal{O}_X(W)$ (viewed in $K(X)$).
--
--   A *reduced simple normal crossing (SNC) boundary* $E$ on a smooth projective variety $X$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim X-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_X(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$. A form $s\in\omega^m_{K(X)}$ is a *log $m$-pluriform* for $(X,E)$ if $t^m s\in L_m(W)$ for every nonempty affine open $W$ and every nonzero $t\in\mathcal{O}_X(W)$ with $\mathcal{I}_E(W)=(t)$; these forms make up a $\mathbb{C}$-subspace $S_m(X,E)\subseteq\omega^m_{K(X)}$, the formal counterpart of $H^0\big(X,m(K_X+E)\big)$.
--
--   Let $E$ be a reduced SNC boundary on a smooth projective variety $X$. Let $V\subseteq X$ be a nonempty affine open with $B:=\mathcal{O}_X(V)$, and let $\iota_V\colon\big(\textstyle\bigwedge^{\dim X}_{B}\Omega_{B/\mathbb{C}}\big)^{\otimes_B m}\to\omega^m_{K(X)}$ be the $B$-linear map induced by $B\to K(X)$, which sends $\bigotimes_j\big(db_{j,1}\wedge\cdots\wedge db_{j,\dim X}\big)$ to the same expression with the $b_{j,i}$ viewed in $K(X)$.
--
--   Let $m\in\mathbb{N}$, let $s\in S_m(X,E)$, and let $t\in B$ be nonzero with $\mathcal{I}_E(V)=(t)$. Then there exists $q\in\big(\textstyle\bigwedge^{\dim X}_{B}\Omega_{B/\mathbb{C}}\big)^{\otimes_B m}$ such that
--   $$
--   s=t^{-m}\,\iota_V(q)\qquad\text{in }\omega^m_{K(X)} .
--   $$
--
--   Thus, on any chart where the boundary has a local equation $t$, a log pluricanonical form is a regular algebraic form $q$ (its *numerator*) divided by $t^m$. Working with the numerator $q$ is how such forms are later restricted to the fibres of a fibration.
--
--   **Formalization Note** The map $q\mapsto t^{-m}\iota_V(q)$ is `logarithmicPullback` applied to $\mathbb{C}$, the ring of sections on $V$, the function field, the degree $\dim X$, the exponent $m$ and $t$; the inverse is taken in the field $K(X)$, where $t$ has nonzero image.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean#L112-L131

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
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_GlobalSpecialization

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

theorem OAI.ReverseLogKodaira.FiberChartSpecialization.local_logarithmic_numerator
    {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (V : X.scheme.affineOpens) [Nonempty V.1]
    (t : Γ(X.scheme, V.1)) (ht : t ≠ 0) (hI : E.ideal.ideal V = Ideal.span {t}) :
    ∃ q : Pluricanonical ℂ Γ(X.scheme, V.1) X.dimension m,
      logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField X.dimension m t q = s := by sorry
