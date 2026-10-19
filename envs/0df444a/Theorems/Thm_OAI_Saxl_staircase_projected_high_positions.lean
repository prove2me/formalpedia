-- Prove2me | Theorems.Thm_OAI_Saxl_staircase_projected_high_positions
-- name    : OAI.Saxl.staircase_projected_high_positions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T23:59:17.831729+00:00
-- url     : https://prove2.me/theorems/64a410eb-9efa-4469-b643-d6e033a3a738
-- title:
--   In the support of the projected staircase vector, high letters sit exactly on the inner staircase $\delta_h$
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) closed under moving up or to the left, and $\ell(\mu)$ is its number of rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of $t(i)$; its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{r_t}\in W_{n,\ell(\mu)}$; and its Specht module is the cyclic subrepresentation $S^t=\langle e_t\rangle\subseteq W_{n,\ell(\mu)}$.
--
--   For $m\in\mathbb{N}$ let $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$ be the staircase diagram; it has $N_m=m(m+1)/2$ cells and $m$ rows. Fix the reference tableau $T_m:[N_m]\to\delta_m$ (a fixed enumeration of the cells) and its transpose $T'_m=\tau\circ T_m$, where $\tau(i,j)=(j,i)$; as $\delta_m$ is self-conjugate, $T'_m$ is again a tableau of shape $\delta_m$. Its column group $C_{T'_m}$ is the group of position permutations preserving the rows of $T_m$, and $r_{T'_m}(i)$ is the column of $T_m(i)$. Identify the alphabet $[m\cdot m]$ with $[m]\times[m]$ and write a word over it as a pair $w=(w^L,w^R)$ of words $w^L,w^R:[N_m]\to[m]$. The *staircase vector* $\Phi_m\in W_{N_m,m\cdot m}$ is the tensor $e_{T'_m}\otimes e_{T_m}$ regrouped position by position:
--   $$\Phi_m(w)=e_{T'_m}(w^L)\,e_{T_m}(w^R).$$
--   For $s\in\mathbb{N}$ the *same-high projection* $P_s$ on $W_{N_m,m\cdot m}$ keeps the coefficient of a pair word $w$ if, for every position $i$, the letters $w^L(i)$ and $w^R(i)$ are either both $\ge s$ or both $<s$, and replaces it by $0$ otherwise; $P_s$ is $S_{N_m}$-equivariant.
--
--   **Theorem.** Let $h,s\in\mathbb{N}$, put $m=h+s$ and $N=N_m$, and let $w=(w^L,w^R)$ be a pair word of length $N$ over $[m]\times[m]$ such that $(P_s\Phi_m)(w)\neq0$. Then for every position $i\in[N]$, writing $T_m(i)=(p,q)$,
--   $$w^L(i)\ge s\iff p+q<h,$$
--   that is, the left letter at position $i$ is high (at least $s$) exactly when the cell of $i$ lies in the inner staircase $\delta_h\subseteq\delta_{h+s}$.
--
--   Since $(P_s\Phi_m)(w)\neq0$ also forces the same-high condition, the right letters $w^R(i)$ have the same high pattern. Thus the whole support of the projected staircase vector lies in one coordinate sector, determined by cutting $\delta_{h+s}$ into the inner staircase $\delta_h$ and the outer band of $s$ antidiagonals. This rigidity is what allows the projected vector to be rewritten as a sector projection and then factorised into an inner-staircase part and a band part.
--
--   **Formalization Note** Positions and letters are `Fin` types; the pair alphabet is `Fin (m*m)`, decoded into $(w^L,w^R)$ by `splitLeft`/`splitRight` (via `finProdFinEquiv`). $\Phi_m$ is `staircaseWord m`, $P_s$ is `sameHighProjection _ _ _ s`, $T_m$ is `stairTableau m` (the canonical tableau `canonicalTableau (staircase m) rfl`) and $T'_m$ is `stairRowTableau m`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/HighProjection.lean#L129-L168

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

theorem OAI.Saxl.staircase_projected_high_positions (h s : ℕ)
    (w : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0 * (staircase (h+s)).colLen 0))
    (hw : sameHighProjection _ _ _ s (staircaseWord (h+s)) w ≠ 0) :
    ∀ i, s ≤ (splitLeft w i).val ↔
      ((stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h) := by sorry
