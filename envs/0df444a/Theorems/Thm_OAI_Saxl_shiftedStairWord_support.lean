-- Prove2me | Theorems.Thm_OAI_Saxl_shiftedStairWord_support
-- name    : OAI.Saxl.shiftedStairWord_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:14:01.017995+00:00
-- url     : https://prove2.me/theorems/f32f55eb-e474-4ed3-a001-dcf748698a69
-- title:
--   Shifting the letters of the staircase vector preserves its Specht constituents
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) closed under moving up or to the left, and $\ell(\mu)$ is its number of rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of $t(i)$; its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{r_t}\in W_{n,\ell(\mu)}$; and its Specht module is the cyclic subrepresentation $S^t=\langle e_t\rangle\subseteq W_{n,\ell(\mu)}$.
--
--   For $m\in\mathbb{N}$ let $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$ be the staircase diagram; it has $N_m=m(m+1)/2$ cells and $m$ rows. Fix the reference tableau $T_m:[N_m]\to\delta_m$ (a fixed enumeration of the cells) and its transpose $T'_m=\tau\circ T_m$, where $\tau(i,j)=(j,i)$; as $\delta_m$ is self-conjugate, $T'_m$ is again a tableau of shape $\delta_m$. Its column group $C_{T'_m}$ is the group of position permutations preserving the rows of $T_m$, and $r_{T'_m}(i)$ is the column of $T_m(i)$. Identify the alphabet $[m\cdot m]$ with $[m]\times[m]$ and write a word over it as a pair $w=(w^L,w^R)$ of words $w^L,w^R:[N_m]\to[m]$. The *staircase vector* $\Phi_m\in W_{N_m,m\cdot m}$ is the tensor $e_{T'_m}\otimes e_{T_m}$ regrouped position by position:
--   $$\Phi_m(w)=e_{T'_m}(w^L)\,e_{T_m}(w^R).$$
--   For $s\in\mathbb{N}$ the *same-high projection* $P_s$ on $W_{N_m,m\cdot m}$ keeps the coefficient of a pair word $w$ if, for every position $i$, the letters $w^L(i)$ and $w^R(i)$ are either both $\ge s$ or both $<s$, and replaces it by $0$ otherwise; $P_s$ is $S_{N_m}$-equivariant.
--
--   Fix $h,s\in\mathbb{N}$ and write $N=N_h$. Let $\Lambda:W_{N,h\cdot h}\to W_{N,(h+s)(h+s)}$ be the linear map induced by shifting both components of every pair letter by $s$, i.e. $\Lambda(\mathbf{1}_w)=\mathbf{1}_{w+s}$ where $(w+s)(i)=(w^L(i)+s,\ w^R(i)+s)$; equivalently, $(\Lambda z)(v)=z(v-s)$ if all letters of both components of $v$ are at least $s$, and $(\Lambda z)(v)=0$ otherwise. The *shifted staircase vector* is $\Phi_h^{+s}=\Lambda\Phi_h$.
--
--   **Theorem.** Let $\mu$ be a Young diagram and $t$ a tableau of shape $\mu$ on $N$ positions. If there is a nonzero $S_N$-equivariant linear map $f:S^t\to\langle\Phi_h\rangle$, then there is a nonzero $S_N$-equivariant linear map
--   $$F:S^t\longrightarrow\langle\Phi_h^{+s}\rangle .$$
--
--   Inside the larger staircase $\delta_{h+s}$ the inner staircase $\delta_h$ is filled with the high letters $s,\dots,h+s-1$, so its contribution to the factorised projected vector is the shifted copy $\Phi_h^{+s}$ rather than $\Phi_h$ itself. The theorem transfers every Specht constituent of the smaller staircase cyclic module to the shifted copy, which is what an induction on the size of the staircase needs.
--
--   **Formalization Note** $\langle\Phi_h\rangle$ is `staircaseCyclic h`; $\Phi_h^{+s}$ is `shiftedStairWord h s = pairLift (highLetter h s) (staircaseWord h)`, where `highLetter h s` is the shift $a\mapsto a+s$ from `Fin h` to `Fin (h+s)` and `pairLift` applies a letter map to both components of a pair letter.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandSupport.lean#L188-L203

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

theorem OAI.Saxl.shiftedStairWord_support (h s : ℕ) (μ : YoungDiagram) (t : Tableau (staircase h).card μ)
    (f : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic h).toRepresentation)
    (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (shiftedStairWord h s)).toRepresentation, F ≠ 0 := by sorry
