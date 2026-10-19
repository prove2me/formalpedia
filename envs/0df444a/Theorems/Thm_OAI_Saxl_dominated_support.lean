-- Prove2me | Theorems.Thm_OAI_Saxl_dominated_support
-- name    : OAI.Saxl.dominated_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:51:10.441988+00:00
-- url     : https://prove2.me/theorems/306e5230-3c84-4978-be31-b7b85ac18b03
-- title:
--   Specht modules of shapes dominated by the staircase map nontrivially into the staircase cyclic module
-- statement:
--   Throughout, $[d]=\{0,1,\dots,d-1\}$. For $n,d\in\mathbb{N}$ let $M_{n,d}$ be the complex vector space of functions on words $w:[n]\to[d]$ (positions $[n]$, letters $[d]$), with basis vectors $\delta_w$ and with the symmetric group $\mathfrak S_n$ acting by $(g\cdot f)(w)=f(w\circ g)$, so that $g\cdot\delta_w=\delta_{w\circ g^{-1}}$. Identifying a letter of $[d^2]$ with a pair of letters in $[d]\times[d]$, a word $w$ over $[d^2]$ is a pair $(w^{(1)},w^{(2)})$ of words over $[d]$, and $(x\boxtimes y)(w)=x(w^{(1)})\,y(w^{(2)})$ defines an $\mathfrak S_n$-equivariant isomorphism $M_{n,d}\otimes M_{n,d}\cong M_{n,d^2}$ (diagonal action on the tensor product).
--
--   A Young diagram $\lambda$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$) closed under moving up or to the left; $\lambda_i$ is the length of row $i$ (zero for empty rows) and $\ell(\lambda)$ the number of nonempty rows. A tableau of shape $\lambda$ with $|\lambda|=n$ is any bijection $t:[n]\to\lambda$ from positions to cells. Its row word $r_t:[n]\to[\ell(\lambda)]$ sends $p$ to the row of $t(p)$; its column group $C_t\le\mathfrak S_n$ consists of the permutations $g$ such that $t(g(p))$ and $t(p)$ lie in the same column for every $p$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\delta_{r_t}\in M_{n,\ell(\lambda)}$; and the Specht module $S^t\subseteq M_{n,\ell(\lambda)}$ is the span of the vectors $g\cdot e_t$, $g\in\mathfrak S_n$.
--
--   The staircase of size $m$ is $\delta_m=\{(i,j)\in\mathbb{N}^2: i+j<m\}$; its row $i$ has $m-i$ cells for $i<m$, it has $m$ rows, and $|\delta_m|=m(m+1)/2$. Let $t_m$ be a fixed (canonical) tableau of $\delta_m$, and let $t_m^{*}$ be its transpose, $t_m^*(p)=(j,i)$ whenever $t_m(p)=(i,j)$; this is again a tableau of $\delta_m$ because $\delta_m$ is self-conjugate, and its column group $C_{t_m^*}$ is the group of permutations preserving the rows of $t_m$. The staircase vector and the staircase cyclic module are
--
--   $$\Omega_m=e_{t_m^*}\boxtimes e_{t_m}\in M_{n,m^2},\qquad C_m=\operatorname{span}\{g\cdot\Omega_m: g\in\mathfrak S_n\}\subseteq M_{n,m^2},\qquad n=|\delta_m|.$$
--
--   For Young diagrams $\lambda,\mu$, say that $\lambda$ dominates $\mu$, written $\lambda\trianglerighteq\mu$, if $\sum_{i<k}\mu_i\le\sum_{i<k}\lambda_i$ for every $k\in\mathbb{N}$.
--
--   **Theorem.** Let $m\ge1$, $n=m(m+1)/2$, let $\mu$ be a Young diagram and $t:[n]\to\mu$ a tableau of shape $\mu$ (so $|\mu|=n$). If the staircase dominates $\mu$, then there is a nonzero $\mathfrak S_n$-equivariant linear map $f:S^t\to C_m$:
--
--   $$\delta_m\trianglerighteq\mu\quad\Longrightarrow\quad\exists\,f\in\operatorname{Hom}_{\mathfrak S_n}(S^t,C_m),\ f\neq0.$$
--
--   Since $S^t$ is irreducible, such an $f$ is injective, so $S^t$ occurs as a subrepresentation of $C_m$. The polytabloid $e_{t_m^*}$ also lies in $S^{t_m}$, so $C_m$ is contained in the image of $S^{t_m}\otimes S^{t_m}$ under the injective map $x\otimes y\mapsto x\boxtimes y$. The theorem therefore shows that every Specht module of a shape dominated by the staircase occurs in the tensor square of the staircase Specht module. It settles the dominated case of the induction over the size of the staircase.
--
--   **Formalization Note** Dominance is `Dominates (staircase m) μ`, i.e. `rowPrefix μ k ≤ rowPrefix (staircase m) k` for all `k`, where `rowPrefix μ k` is the sum of the first `k` row lengths. Equivariant maps are `Representation.IntertwiningMap`, $C_m$ is `staircaseCyclic m`, and the tableau `t` is an arbitrary bijection `Fin (staircase m).card ≃ μ.cells`, not necessarily standard. The hypothesis $m\ge1$ is part of the statement but is not used in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean#L158-L208

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
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedQuotient
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedSupport

open OAI OAI.Saxl
open scoped TensorProduct
universe uX uY

theorem OAI.Saxl.dominated_support (m : ℕ) (_hm : 1 ≤ m) (μ : YoungDiagram)
    (t : Tableau (staircase m).card μ) (hμ : Dominates (staircase m) μ) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic m).toRepresentation, f ≠ 0 := by sorry
