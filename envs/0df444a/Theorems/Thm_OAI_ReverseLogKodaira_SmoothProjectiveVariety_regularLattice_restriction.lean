-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_regularLattice_restriction
-- name    : OAI.ReverseLogKodaira.SmoothProjectiveVariety.regularLattice_restriction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:49:07.96983+00:00
-- url     : https://prove2.me/theorems/6b56b2a2-73ac-434d-b1a4-fe8f56c16b48
-- title:
--   Pluricanonical forms regular on an affine open remain regular on smaller affine opens
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field. For a smooth projective variety $X$, write $\omega^m_{K(X)}=\big(\textstyle\bigwedge^{\dim X}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m}$ for the one-dimensional $K(X)$-vector space of rational $m$-pluricanonical forms. For a nonempty affine open $W\subseteq X$, the *regular lattice* $L_m(W)\subseteq\omega^m_{K(X)}$ is the $\mathcal{O}_X(W)$-submodule spanned by all forms $\bigotimes_{j=1}^{m}\big(da_{j,1}\wedge\cdots\wedge da_{j,\dim X}\big)$ with $a_{j,i}\in\mathcal{O}_X(W)$ (viewed in $K(X)$).
--
--   Let $X$ be a smooth projective variety. For nonempty affine opens $U\subseteq V$ of $X$ and every $m\in\mathbb{N}$,
--   $$
--   L_m(V)\subseteq L_m(U).
--   $$
--
--   In words: a rational pluricanonical form that is regular on $V$ is regular on every smaller nonempty affine open. Together with the locality of the regular lattice, this allows one to pass between different affine charts when checking that a pluricanonical form is regular or has logarithmic poles along a boundary.
--
--   **Formalization Note** $L_m(W)$ is `X.regularPluriformLattice W m`, a submodule over the ring of sections on $W$ of `X.RationalPluriform m`. The nonemptiness assumptions are needed because the map from the sections on $W$ to $K(X)$ is the germ at the generic point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/LogLattice.lean#L136-L157

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

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem OAI.ReverseLogKodaira.SmoothProjectiveVariety.regularLattice_restriction (X : SmoothProjectiveVariety)
    (U V : X.scheme.affineOpens) [Nonempty U.1] [Nonempty V.1] (hUV : U.1 ≤ V.1)
    (m : ℕ) {s : X.RationalPluriform m} (hs : s ∈ X.regularPluriformLattice V m) :
    s ∈ X.regularPluriformLattice U m := by sorry
