-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_ReducedSNCBoundary_kodaira_eq_bot_iff
-- name    : OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.kodaira_eq_bot_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:54:42.915922+00:00
-- url     : https://prove2.me/theorems/eef1288d-129b-43c0-b305-2cd4dbe4f259
-- title:
--   The log Kodaira dimension is $-\infty$ exactly when all log pluricanonical forms of positive degree vanish
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; every ring of sections $\mathcal{O}_Z(W)$ is a $\mathbb{C}$-algebra through the structure morphism, and $K(Z)$ denotes the function field. For a smooth projective variety $X$, write $\omega^m_{K(X)}=\big(\textstyle\bigwedge^{\dim X}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m}$ for the $K(X)$-vector space of rational $m$-pluricanonical forms. For a nonempty affine open $W\subseteq X$, the *regular lattice* $L_m(W)\subseteq\omega^m_{K(X)}$ is the $\mathcal{O}_X(W)$-submodule spanned by all forms $\bigotimes_{j=1}^{m}\big(da_{j,1}\wedge\cdots\wedge da_{j,\dim X}\big)$ with $a_{j,i}\in\mathcal{O}_X(W)$ (viewed in $K(X)$).
--
--   A *reduced simple normal crossing (SNC) boundary* $E$ on a smooth projective variety $X$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim X-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_X(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$. A form $s\in\omega^m_{K(X)}$ is a *log $m$-pluriform* for $(X,E)$ if $t^m s\in L_m(W)$ for every nonempty affine open $W$ and every nonzero $t\in\mathcal{O}_X(W)$ with $\mathcal{I}_E(W)=(t)$; these forms make up a $\mathbb{C}$-subspace $S_m(X,E)\subseteq\omega^m_{K(X)}$, the formal counterpart of $H^0\big(X,m(K_X+E)\big)$.
--
--   The *log Kodaira dimension* of $(X,E)$ is defined as follows. For $k\in\mathbb{N}$, say that $(X,E)$ *has image dimension at least $k$* if there exist $m>0$, a nonzero $s\in S_m(X,E)$ and elements $r_1,\dots,r_k\in K(X)$, algebraically independent over $\mathbb{C}$, such that $r_i\,s\in S_m(X,E)$ for $i=1,\dots,k$. Then
--   $$
--   \kappa(X,E):=\sup\{\,k\in\mathbb{N}\ :\ (X,E)\text{ has image dimension at least }k\,\}\ \in\ \{-\infty\}\cup\mathbb{N}\cup\{\infty\},
--   $$
--   where the supremum of the empty set is $-\infty$.
--
--   **Theorem.** Let $X$ be a smooth projective variety and $E$ a reduced SNC boundary on $X$. Then
--   $$
--   \kappa(X,E)=-\infty\iff\text{for every integer } m>0 \text{ and every } s\in S_m(X,E):\ s=0 .
--   $$
--
--   This is the familiar characterisation "$\kappa=-\infty$ if and only if $H^0\big(X,m(K_X+E)\big)=0$ for all $m\ge1$" in the present formal setting. It converts statements about log Kodaira dimension $-\infty$, on the total space or on the fibres of a fibration, into vanishing or nonvanishing statements for individual log pluricanonical forms.
--
--   **Formalization Note** $\kappa(X,E)$ is `E.kodaira`, a value in `WithBot ℕ∞` defined as an indexed supremum, and $-\infty$ is its bottom element $\bot$. The predicate "has image dimension at least $k$" is `E.HasImageDimensionAtLeast k`, and $S_m(X,E)$ is the $\mathbb{C}$-subspace `E.sections m` of `X.RationalPluriform m`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/Basic.lean#L344-L361

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

theorem OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.kodaira_eq_bot_iff {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) :
    E.kodaira = ⊥ ↔ ∀ (m : ℕ), 0 < m →
      ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0 := by sorry
