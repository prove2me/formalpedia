-- Prove2me | Theorems.Thm_OAI_Saxl_staircase_cut_layers
-- name    : OAI.Saxl.staircase_cut_layers
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:01:32.717818+00:00
-- url     : https://prove2.me/theorems/2608ff51-3f49-43d6-99b7-47d1ecfbb24c
-- title:
--   The same-high projection of the staircase vector factors exactly into two signed layers
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) closed under moving up or to the left, and $\ell(\mu)$ is its number of rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of $t(i)$; its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{r_t}\in W_{n,\ell(\mu)}$; and its Specht module is the cyclic subrepresentation $S^t=\langle e_t\rangle\subseteq W_{n,\ell(\mu)}$.
--
--   For $m\in\mathbb{N}$ let $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$ be the staircase diagram; it has $N_m=m(m+1)/2$ cells and $m$ rows. Fix the reference tableau $T_m:[N_m]\to\delta_m$ (a fixed enumeration of the cells) and its transpose $T'_m=\tau\circ T_m$, where $\tau(i,j)=(j,i)$; as $\delta_m$ is self-conjugate, $T'_m$ is again a tableau of shape $\delta_m$. Its column group $C_{T'_m}$ is the group of position permutations preserving the rows of $T_m$, and $r_{T'_m}(i)$ is the column of $T_m(i)$. Identify the alphabet $[m\cdot m]$ with $[m]\times[m]$ and write a word over it as a pair $w=(w^L,w^R)$ of words $w^L,w^R:[N_m]\to[m]$. The *staircase vector* $\Phi_m\in W_{N_m,m\cdot m}$ is the tensor $e_{T'_m}\otimes e_{T_m}$ regrouped position by position:
--   $$\Phi_m(w)=e_{T'_m}(w^L)\,e_{T_m}(w^R).$$
--   For $s\in\mathbb{N}$ the *same-high projection* $P_s$ on $W_{N_m,m\cdot m}$ keeps the coefficient of a pair word $w$ if, for every position $i$, the letters $w^L(i)$ and $w^R(i)$ are either both $\ge s$ or both $<s$, and replaces it by $0$ otherwise; $P_s$ is $S_{N_m}$-equivariant.
--
--   Now fix $h,s\in\mathbb{N}$, put $m=h+s$, $N=N_m$, $T=T_m$, $T'=T'_m$. Let $D=\{i\in[N]:T(i)\in\delta_h\}$ be the positions whose cell lies in the inner staircase, and $\mathrm{Stab}(D)=\{g\in S_N:g(D)=D\}$. The row rotation $R$ and the column rotation $C=\tau R\tau$ of $\delta_{h+s}$ are
--   $$R(i,j)=\begin{cases}(i,\,j+s)&i+j<h,\\ (i,\,j-\max(h-i,0))&i+j\ge h,\end{cases}\qquad C(i,j)=\begin{cases}(i+s,\,j)&i+j<h,\\ (i-\max(h-j,0),\,j)&i+j\ge h;\end{cases}$$
--   $R$ preserves rows and $C$ preserves columns. Let $\rho=T^{-1}RT\in C_{T'}$ and $\kappa=T^{-1}CT\in C_T$ be the corresponding position permutations, and $a=r_{T'}\circ\rho$, $b=r_T\circ\kappa$ the rotated words, so $a(i)$ is the column of $R(T(i))$ and $b(i)$ the row of $C(T(i))$. The two *cut layers* are the signed alternations
--   $$\Theta^{\mathrm{row}}_{h,s}=\sum_{g\in C_{T'}\cap\mathrm{Stab}(D)}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{a},\qquad \Theta^{\mathrm{col}}_{h,s}=\sum_{g\in C_{T}\cap\mathrm{Stab}(D)}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{b}$$
--   in $W_{N,m}$.
--
--   **Theorem.** For every pair word $w=(w^L,w^R)$ of length $N$ over $[m]\times[m]$,
--   $$(P_s\Phi_{h+s})(w)=\Theta^{\mathrm{row}}_{h,s}(w^L)\,\Theta^{\mathrm{col}}_{h,s}(w^R),$$
--   that is, $P_s\Phi_{h+s}$ is the regrouped tensor $\Theta^{\mathrm{row}}_{h,s}\otimes\Theta^{\mathrm{col}}_{h,s}$.
--
--   This is an exact factorisation with no leftover scalar: the signs produced by the two rotations cancel. After projection, both tensor factors only involve permutations that preserve the set $D$ of inner-staircase positions, which is the starting point for splitting each layer further into a part on $\delta_h$ (a shifted copy of the smaller staircase) and a part on the band $\delta_{h+s}\setminus\delta_h$.
--
--   **Formalization Note** $\Theta^{\mathrm{row}}_{h,s}$ and $\Theta^{\mathrm{col}}_{h,s}$ are `cutRowWord h s` and `cutColumnWord h s`, defined as `altWord` over `columnGroup (stairRowTableau (h+s)) ⊓ sectorGroup (stairHigh h s)` and `columnGroup (stairTableau (h+s)) ⊓ sectorGroup (stairHigh h s)`; the regrouping isomorphism is `wordTensor`, and the subtraction in $R$ and $C$ is the truncated natural subtraction of the source, which agrees with the formulas above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/CoordinateSector.lean#L180-L203

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

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.staircase_cut_layers (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
      wordTensor _ _ _ (cutRowWord h s ⊗ₜ[ℂ] cutColumnWord h s) := by sorry
