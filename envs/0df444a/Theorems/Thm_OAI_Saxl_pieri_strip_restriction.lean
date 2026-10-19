-- Prove2me | Theorems.Thm_OAI_Saxl_pieri_strip_restriction
-- name    : OAI.Saxl.pieri_strip_restriction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:27:20.87499+00:00
-- url     : https://prove2.me/theorems/29c3565e-09f5-4bd1-b600-be773fc346a6
-- title:
--   A nonzero Pieri restriction map between Specht modules for a horizontal strip
-- statement:
--   Write $[m]=\{0,1,\dots,m-1\}$ and let $S_m$ be the symmetric group on $[m]$. For $m,d\in\mathbb{N}$ let $W_{m,d}$ be the space of functions from words $w:[m]\to[d]$ to $\mathbb{C}$, on which $S_m$ acts by $(g\cdot x)(w)=x(w\circ g)$; thus the indicator $\delta_w$ of a word is sent to $\delta_{w\circ g^{-1}}$. A Young diagram $\lambda$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ ($i$ the row, $j$ the column) that is closed under moving up or to the left; $|\lambda|$ is its number of cells and $\ell(\lambda)$ its number of rows. A tableau of shape $\lambda$ on $[m]$ is a bijection $t:[m]\to\lambda$ (so $|\lambda|=m$). Its row word $r_t:[m]\to[\ell(\lambda)]$ sends $k$ to the row of $t(k)$; its column group $C_t\le S_m$ consists of the permutations $g$ such that $t(g(k))$ and $t(k)$ lie in the same column for every $k$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\delta_{r_t}\in W_{m,\ell(\lambda)}$; and its Specht module $S^t\subseteq W_{m,\ell(\lambda)}$ is the $S_m$-invariant subspace spanned by $\{g\cdot e_t: g\in S_m\}$, with the restricted action.
--
--   For Young diagrams $\nu\subseteq\mu$, the skew shape $\mu/\nu$ is a *horizontal strip* if $\mu\setminus\nu$ contains at most one cell in each column. For tableaux $s:[a]\to\nu$ and $t:[n]\to\mu$ with $\nu\subseteq\mu$, let $\iota_{s,t}:[a]\to[n]$, $\iota_{s,t}(k)=t^{-1}(s(k))$, be the injective map sending a position of $s$ to the position that $t$ assigns to the same cell.
--
--   Let $\nu\subseteq\mu$ be Young diagrams such that $\mu/\nu$ is a horizontal strip, let $s:[a]\to\nu$ and $t:[n]\to\mu$ be tableaux, and write $\iota=\iota_{s,t}$. Then there is a linear map $F:S^t\to S^s$ with $F\neq0$ such that, for all $g\in S_n$ and $h\in S_a$ with $g(\iota(k))=\iota(h(k))$ for every $k\in[a]$,
--   $$
--   F(g\cdot x)=h\cdot F(x)\qquad\text{for all }x\in S^t .
--   $$
--
--   In particular, $F$ is a nonzero homomorphism of representations of the subgroup of $S_n$ that maps $\iota([a])$ onto itself (a copy of $S_a\times S_{n-a}$), from $S^t$ to $S^s$, where this subgroup acts on $S^s$ through its action on $\iota([a])$ and the permutations of the strip positions act trivially. This is the existence part of the horizontal-strip Pieri rule, realized concretely in the polytabloid model.
--
--   **Formalization Note** The strip condition is `HorizontalStrip ν μ` (its first component `hs.1` is the inclusion $\nu\subseteq\mu$), $\iota$ is `tableauInclusion s t hs.1`, $S^t$ is the submodule `Specht t` with action `spechtRep t`, and $F$ is a linear map whose equivariance is stated only for compatible pairs $(g,h)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/PieriRestriction.lean#L201-L222

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.pieri_strip_restriction {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, F ≠ 0 ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by sorry
