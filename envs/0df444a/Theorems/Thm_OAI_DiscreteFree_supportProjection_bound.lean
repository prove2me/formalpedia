-- Prove2me | Theorems.Thm_OAI_DiscreteFree_supportProjection_bound
-- name    : OAI.DiscreteFree.supportProjection_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:58:03.244716+00:00
-- url     : https://prove2.me/theorems/e60dba14-2065-44d7-b7b9-d57a0cb06eaa
-- title:
--   Finite-support projections on the free space of a bounded uniformly discrete space have norm at most $2B$
-- statement:
--   Let $(M,d)$ be a metric space with a base point $o$ that is uniformly discrete with constant $1$: $d(x,y)\ge1$ whenever $x\neq y$. Let $\mathrm{Lip}_0(M)$ be the space of Lipschitz functions $f:M\to\mathbb{R}$ with $f(o)=0$, normed by the best Lipschitz constant $\|f\|_L=\sup_{x\neq y}|f(x)-f(y)|/d(x,y)$. The Lipschitz-free space $\mathcal F(M)$ is the closed linear span, in the dual space $\mathrm{Lip}_0(M)^*$, of the evaluation functionals $\delta(x):f\mapsto f(x)$, $x\in M$, with the dual norm; we write $\langle u,f\rangle$ for $u\in\mathcal F(M)$ applied to $f\in\mathrm{Lip}_0(M)$.
--
--   For $j\in M$ let $\chi_j$ be the indicator function of $\{j\}$ if $j\neq o$, and $\chi_o=0$. By the separation assumption $\chi_j\in\mathrm{Lip}_0(M)$, so $c_j(u)=\langle u,\chi_j\rangle$ is a bounded linear functional on $\mathcal F(M)$; it satisfies $c_j(\delta(x))=1$ if $x=j\neq o$ and $c_j(\delta(x))=0$ otherwise. For a finite set $F\subseteq M$ the *support projection* is the finite-rank operator
--   $$P_F:\mathcal F(M)\to\mathcal F(M),\qquad P_Fu=\sum_{j\in F}c_j(u)\,\delta(j).$$
--
--   **Theorem.** Let $B\ge0$ and suppose that $d(x,o)\le B$ for every $x\in M$. Then for every finite set $F\subseteq M$
--   $$
--   \|P_F\|\le 2B .
--   $$
--
--   The operator $P_F$ fixes $\delta(x)$ for $x\in F$ and annihilates $\delta(x)$ for $x\notin F$. The uniform bound $2B$, independent of $F$, is what makes these projections usable as bounded approximants of the identity: it yields the bounded approximation property of $\mathcal F(M)$ with constant $2B$ for bounded uniformly discrete $M$, and it controls the error when finite-rank operators are compressed to finitely many coordinates.
--
--   **Formalization Note** The separation hypothesis is the section variable `sep`, which is needed to define $\chi_j$ (`indicator o sep j`), $c_j$ (`coordinate o sep j`) and $P_F$ (`supportProjection o sep F`). The norm is the operator norm of continuous linear maps from `FreeSpace o` to itself.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Coordinates.lean#L139-L151

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

open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem OAI.DiscreteFree.supportProjection_bound (F : Finset M) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, dist x o ≤ B) : ‖supportProjection o sep F‖ ≤ 2*B := by sorry
