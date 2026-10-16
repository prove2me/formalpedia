-- Prove2me | Theorems.Thm_OAI_DiscreteFree_affine_difference_bound
-- name    : OAI.DiscreteFree.affine_difference_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T10:01:04.163292+00:00
-- url     : https://prove2.me/theorems/c8a160ef-7692-40c4-a40e-325dada372d1
-- title:
--   One-Lipschitz tests separate the affine weights of $T\delta(x)$ and $T\delta(y)$ by at most $c\,d(x,y)$
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$ such that $d(x,y)\ge1$ whenever $x\ne y$, let $S\subseteq M$ be finite with $o\in S$, and let $\mathcal F(M)$ be the Lipschitz-free space of $(M,o)$: the closed linear span of the evaluation functionals $\delta(x):f\mapsto f(x)$ in the dual of the space of real Lipschitz functions on $M$ vanishing at $o$, normed by the best Lipschitz constant. For $j\in M$ let $c_j(u)=\langle u,\chi_j\rangle$ with $\chi_j$ the indicator of $\{j\}$ if $j\ne o$ and $\chi_o=0$, let $P_Su=\sum_{j\in S}c_j(u)\,\delta(j)$, and let
--   $$\mu_u(j)=c_j(u)+[\,j=o\,]\Bigl(1-\sum_{k\in S}c_k(u)\Bigr)\qquad(j\in S)$$
--   be the affine weights of $u\in\mathcal F(M)$, where $[\,j=o\,]$ is $1$ if $j=o$ and $0$ otherwise (so $\sum_{j\in S}\mu_u(j)=1$).
--
--   **Theorem.** Let $T$ be a bounded linear operator on $\mathcal F(M)$ with $P_S(Tu)=Tu$ for every $u\in\mathcal F(M)$, let $c$ be a real number with $\|T\|\le c$, and let $g:M\to\mathbb{R}$ be $1$-Lipschitz. Then for all $x,y\in M$
--   $$
--   \Bigl|\sum_{j\in S}\mu_{T\delta(x)}(j)\,g(j)-\sum_{j\in S}\mu_{T\delta(y)}(j)\,g(j)\Bigr|\le c\,d(x,y).
--   $$
--
--   This is the upper half of a per-edge test: if $x$ and $y$ are points at distance at most $1$ and $\|T\|\le 2p$, no $1$-Lipschitz function distinguishes the affine weights of $T\delta(x)$ and $T\delta(y)$ by more than $2p$. It is played against lower bounds coming from bump functions to obtain a contradiction for operators of small norm.
--
--   **Formalization Note** The weights are `affineWeights o sep S ho`, the sums are `pairing`, and $g$ is assumed `LipschitzWith 1 g`. The bound $\|T\|\le c$ forces $c\ge0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/AffineWeights.lean#L92-L112

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights

open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

theorem OAI.DiscreteFree.affine_difference_bound (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (c : ℝ) (hn : ‖T‖ ≤ c)
    (g : M → ℝ) (hg : LipschitzWith 1 g) (x y : M) :
    |pairing (affineWeights o sep S ho (T (delta o x))) (fun j : S => g j.val) -
      pairing (affineWeights o sep S ho (T (delta o y))) (fun j : S => g j.val)| ≤
        c * dist x y := by sorry
