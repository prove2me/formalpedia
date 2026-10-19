-- Prove2me | Theorems.Thm_OAI_Saxl_twoBand_support
-- name    : OAI.Saxl.twoBand_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:11:32.572221+00:00
-- url     : https://prove2.me/theorems/5e602ba6-c1b8-4d5c-b7ba-d38c1d2957e3
-- title:
--   Every Specht module with at most four rows maps into the cyclic module of the two-antidiagonal staircase band
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) closed under moving up or to the left, and $\ell(\mu)$ is its number of rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of $t(i)$; its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{r_t}\in W_{n,\ell(\mu)}$; and its Specht module is the cyclic subrepresentation $S^t=\langle e_t\rangle\subseteq W_{n,\ell(\mu)}$.
--
--   Fix $h\ge1$ and consider the staircase $\delta_{h+2}=\{(i,j):i+j<h+2\}$ with its reference tableau $T_{h+2}$ (a fixed enumeration of its cells). The *band* is the set $B=\{(i,j):h\le i+j\le h+1\}$ of cells on the two outermost antidiagonals; it has $2h+3$ cells. Its positions are numbered by $[2h+3]$ through a fixed bijection $\beta:[2h+3]\to B$ (the positions of $T_{h+2}$ whose cells lie outside $\delta_h$, renumbered). For a band cell $(i,j)$ define the two letters
--   $$a(i,j)=j-\max(h-i,0),\qquad b(i,j)=i-\max(h-j,0),$$
--   both in $\{0,1\}$, regarded as letters of $[h+2]$. Let $\mathrm{Row}(\beta)\le S_{2h+3}$ (respectively $\mathrm{Col}(\beta)$) be the permutations $g$ such that $\beta(g(p))$ lies in the same row (respectively column) as $\beta(p)$ for every $p$. The two band layers and the *band vector* are
--   $$\Theta^{\mathrm{row}}=\sum_{g\in\mathrm{Row}(\beta)}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{a\circ\beta},\qquad\Theta^{\mathrm{col}}=\sum_{g\in\mathrm{Col}(\beta)}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{b\circ\beta},\qquad\Psi_h(w)=\Theta^{\mathrm{row}}(w^L)\,\Theta^{\mathrm{col}}(w^R),$$
--   where $\Theta^{\mathrm{row}},\Theta^{\mathrm{col}}\in W_{2h+3,h+2}$ and $\Psi_h\in W_{2h+3,(h+2)(h+2)}$ is a function of pair words $w=(w^L,w^R)$ over $[h+2]\times[h+2]$.
--
--   **Theorem.** Let $h\ge1$, let $\mu$ be a Young diagram with at most four rows, $\ell(\mu)\le4$, and let $t$ be a tableau of shape $\mu$ on the $2h+3$ band positions. Then there is a nonzero $S_{2h+3}$-equivariant linear map
--   $$f:S^t\longrightarrow\langle\Psi_h\rangle\subseteq W_{2h+3,(h+2)(h+2)}.$$
--
--   The letters $a$ and $b$ are the column, respectively row, indices of the band cells after the row and column rotations that move the inner staircase $\delta_h$ to the high letters, so $\Psi_h$ is the band factor of the two layers of the projected staircase vector of $\delta_{h+2}$. The theorem says that its cyclic module contains every Specht module of $S_{2h+3}$ with at most four rows; this is the base case for the band layers in the inductive approach to the staircase tensor square.
--
--   **Formalization Note** The number of band positions is `bandSize h 2`, defined as the number of positions of $T_{h+2}$ outside $\delta_h$ (equal to $2h+3$); $\beta$ is `bandTableau h 2`, the layers are `bandRowWord h 2` and `bandColumnWord h 2`, and $\Psi_h$ is `stairBandWord h 2`, built with the regrouping isomorphism `wordTensor` on the pair alphabet `Fin ((h+2)*(h+2))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandSupport.lean#L45-L61

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

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.twoBand_support (h : ℕ) (hh : 1 ≤ h) (μ : YoungDiagram)
    (t : Tableau (bandSize h 2) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (stairBandWord h 2)).toRepresentation, f ≠ 0 := by sorry
