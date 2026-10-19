-- Prove2me | Theorems.Thm_OAI_Saxl_staircase_projected_ne_zero
-- name    : OAI.Saxl.staircase_projected_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:00:57.743818+00:00
-- url     : https://prove2.me/theorems/9818b6e8-2c99-4c17-8632-28c1560d4305
-- title:
--   The same-high projection of the staircase tensor vector is nonzero
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) closed under moving up or to the left, and $\ell(\mu)$ is its number of rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of $t(i)$; its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{r_t}\in W_{n,\ell(\mu)}$; and its Specht module is the cyclic subrepresentation $S^t=\langle e_t\rangle\subseteq W_{n,\ell(\mu)}$.
--
--   For $m\in\mathbb{N}$ let $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$ be the staircase diagram; it has $N_m=m(m+1)/2$ cells and $m$ rows. Fix the reference tableau $T_m:[N_m]\to\delta_m$ (a fixed enumeration of the cells) and its transpose $T'_m=\tau\circ T_m$, where $\tau(i,j)=(j,i)$; as $\delta_m$ is self-conjugate, $T'_m$ is again a tableau of shape $\delta_m$. Its column group $C_{T'_m}$ is the group of position permutations preserving the rows of $T_m$, and $r_{T'_m}(i)$ is the column of $T_m(i)$. Identify the alphabet $[m\cdot m]$ with $[m]\times[m]$ and write a word over it as a pair $w=(w^L,w^R)$ of words $w^L,w^R:[N_m]\to[m]$. The *staircase vector* $\Phi_m\in W_{N_m,m\cdot m}$ is the tensor $e_{T'_m}\otimes e_{T_m}$ regrouped position by position:
--   $$\Phi_m(w)=e_{T'_m}(w^L)\,e_{T_m}(w^R).$$
--   For $s\in\mathbb{N}$ the *same-high projection* $P_s$ on $W_{N_m,m\cdot m}$ keeps the coefficient of a pair word $w$ if, for every position $i$, the letters $w^L(i)$ and $w^R(i)$ are either both $\ge s$ or both $<s$, and replaces it by $0$ otherwise; $P_s$ is $S_{N_m}$-equivariant.
--
--   **Theorem.** For all $h,s\in\mathbb{N}$,
--   $$P_s\,\Phi_{h+s}\neq0 .$$
--
--   The projection $P_s$ discards every coefficient of the staircase vector in which some position carries one high and one low letter. The theorem guarantees that something always survives, for every way of cutting $\delta_{h+s}$ into the inner staircase $\delta_h$ and an outer band of $s$ antidiagonals (including the degenerate cases $h=0$ or $s=0$). Since $P_s$ is equivariant, it maps the cyclic module $\langle\Phi_{h+s}\rangle$ onto $\langle P_s\Phi_{h+s}\rangle$, which is therefore a nonzero representation; this nonvanishing is needed when the projected vector is factorised into two layers and used in the inductive treatment of the staircase.
--
--   **Formalization Note** $\Phi_m$ is `staircaseWord m`, $P_s$ is `sameHighProjection _ _ _ s` (an intertwiner of the word representation on the pair alphabet `Fin (m*m)`), and the statement is the inequality of this intertwiner applied to $\Phi_{h+s}$ with the zero vector.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/HighProjection.lean#L257-L286

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.staircase_projected_ne_zero (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) ≠ 0 := by sorry
