-- Prove2me | Theorems.Thm_OAI_Saxl_Columns_mapped_columnTableau
-- name    : OAI.Saxl.Columns.mapped_columnTableau
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:06:59.931395+00:00
-- url     : https://prove2.me/theorems/05800073-5d87-4b2e-81d9-fc680db18148
-- title:
--   The column-reading polytabloid under a matrix-valued letter map is a signed sum of pure matrix tensors
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) closed under moving up or to the left, and $\ell(\mu)$ is its number of rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of $t(i)$; its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{r_t}\in W_{n,\ell(\mu)}$; and its Specht module is the cyclic subrepresentation $S^t=\langle e_t\rangle\subseteq W_{n,\ell(\mu)}$.
--
--   Let $\mu$ be a Young diagram with $k$ columns of lengths $c_0\ge c_1\ge\cdots\ge c_{k-1}\ge1$, so that $n=|\mu|=c_0+\cdots+c_{k-1}$ and $\ell=\ell(\mu)$ is its number of rows. The *column-reading tableau* $T^{\mathrm{col}}:[n]\to\mu$ numbers the cells column by column, each column from top to bottom: position $c_0+\cdots+c_{j-1}+i$ is the cell $(i,j)$, for $0\le i<c_j$.
--
--   Identify the four-letter alphabet $[4]$ with $[2]\times[2]$, writing a letter as $(x,y)$, so that $W_{n,4}$ is the coordinate space of $(\mathbb{C}^{2\times2})^{\otimes n}$. For matrices $X_0,\dots,X_{n-1}\in\mathbb{C}^{2\times2}$ the pure tensor $X_0\otimes\cdots\otimes X_{n-1}\in W_{n,4}$ is the function $w\mapsto\prod_{q}(X_q)_{x_q\,y_q}$, where $w(q)=(x_q,y_q)$. Given a sequence $N_0,N_1,N_2,\dots$ of complex $2\times2$ matrices, let $\Lambda_N:W_{n,\ell}\to W_{n,4}$ be the $n$-fold tensor power of the linear map sending the letter $i\in[\ell]$ to the matrix $N_i$; explicitly $(\Lambda_N z)(w)=\sum_{a\in[\ell]^{n}}z(a)\prod_q(N_{a(q)})_{x_q\,y_q}$.
--
--   **Theorem.** With these notations,
--   $$\Lambda_N\bigl(e_{T^{\mathrm{col}}}\bigr)=\sum_{\pi_0\in S_{c_0}}\cdots\sum_{\pi_{k-1}\in S_{c_{k-1}}}\Bigl(\prod_{j=0}^{k-1}\operatorname{sgn}\pi_j\Bigr)\;\bigotimes_{j=0}^{k-1}\ \bigotimes_{i=0}^{c_j-1}N_{\pi_j(i)},$$
--   where $S_c$ is the group of permutations of $[c]$ and the tensor factors are ordered by position, that is, column by column and from top to bottom within a column: the factor at the position of the cell $(i,j)$ is $N_{\pi_j(i)}$.
--
--   The formula turns the polytabloid of the column-reading tableau into a signed sum of pure matrix tensors, one for each independent choice of a permutation of every column. Contracting such tensors with a matrix-product functional then factorises column by column, which is how nonvanishing of certain band pairings is computed.
--
--   **Formalization Note** The column lengths are the list `μ.transpose.rowLens`, $T^{\mathrm{col}}$ is `Columns.columnTableau μ`, the tuples $(\pi_j)$ form `Perms μ.transpose.rowLens` with sign `sg π`, the identification of `Fin 4` with pairs is `Path.parts` (via `finProdFinEquiv`), $\Lambda_N$ is `wordMap` with kernel $(i,a)\mapsto N_i$ evaluated at the pair $a$, and the pure tensor is `Path.pureWord`. The family $N$ is indexed by all of $\mathbb{N}$, but only $N_0,\dots,N_{\ell-1}$ matter.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/ColumnContraction.lean#L272-L304

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

open OAI OAI.Saxl OAI.Saxl.Columns
open scoped TensorProduct

theorem OAI.Saxl.Columns.mapped_columnTableau (μ : YoungDiagram) (N : ℕ → Band.Mat) :
    wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
      N i.val (Path.parts a).1 (Path.parts a).2) (polytabloid (columnTableau μ)) =
    ∑ π : Perms μ.transpose.rowLens, sg π • Path.pureWord
      (fun q => N (row (perm π (enumerate μ.transpose.rowLens q)))) := by sorry
