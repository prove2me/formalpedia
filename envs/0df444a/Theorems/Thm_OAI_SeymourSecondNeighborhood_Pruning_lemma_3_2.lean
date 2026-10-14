-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_2
-- name    : OAI.SeymourSecondNeighborhood.Pruning.lemma_3_2
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-13T20:27:01.261241+00:00
-- url     : https://prove2.me/theorems/87028f49-7fad-473b-b24b-f8cf4cf9934b
-- title:
--   Lemma 3.2 (kernels at maximum support rank): if a real matrix has maximum rank among matrices with a given support $T$, then $x_jy_s=0$ for $x\in\ker D$, $y\in\ker D^{\mathsf T}$ and $(s,j)\in T$
-- statement:
--   Let $I,J$ be finite index sets and $T\subseteq I\times J$. A real matrix is *supported on* $T$ if its entries outside $T$ are zero (entries in $T$ may vanish). Suppose $D\in\mathbb R^{I\times J}$ is supported on $T$ and has maximum rank among all real matrices supported on $T$. Then for every $x\in\ker D$ (that is, $Dx=0$), every $y\in\ker D^{\mathsf T}$ (that is, $D^{\mathsf T}y=0$) and every $(s,j)\in T$,
--   $$x_j\,y_s=0 .$$
--   This is Lemma 3.2 of the manuscript. Proof idea: if $x_jy_s\neq0$, the perturbed matrix $D'=D+e_se_j^{\mathsf T}$ is still supported on $T$; $D'x=x_je_s$ shows $e_s\in\operatorname{im}D'$, and $Dw=D'w-w_je_s$ shows $\operatorname{im}D\subseteq\operatorname{im}D'$; but $y$ annihilates $\operatorname{im}D$ and $y_s\neq0$, so $e_s\notin\operatorname{im}D$, whence $\operatorname{rank}D'>\operatorname{rank}D$, a contradiction. The lemma is used in the proof of the pruning lemma (`Pruning.lemma_3_1`) to compare restrictions of kernel vectors of two matrices.
-- source:
--   Statement extracted from OpenAI, *A proof of Seymour's second-neighborhood conjecture*, preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood.Pruning

theorem lemma_3_2 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (T : Finset (I × J)) (D : Matrix I J ℝ) (hD : ∀ i j, (i, j) ∉ T → D i j = 0)
    (hmax : ∀ D' : Matrix I J ℝ, (∀ i j, (i, j) ∉ T → D' i j = 0) → D'.rank ≤ D.rank)
    (x : J → ℝ) (hx : D.mulVec x = 0) (y : I → ℝ) (hy : D.transpose.mulVec y = 0)
    (s : I) (j : J) (hsj : (s, j) ∈ T) : x j * y s = 0 := by
  sorry

end OAI.SeymourSecondNeighborhood.Pruning
