-- Prove2me | Theorems.Thm_OAI_DiscreteFree_affineWeights_pairing
-- name    : OAI.DiscreteFree.affineWeights_pairing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T10:00:31.196996+00:00
-- url     : https://prove2.me/theorems/4e6fa9b4-d280-4417-95d2-19f4c86654ac
-- title:
--   Affine weights of a finitely supported element of the free space represent its pairing with Lipschitz functions
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$ such that $d(x,y)\ge1$ whenever $x\ne y$, and let $S\subseteq M$ be a finite set with $o\in S$. Let $\mathcal F(M)$ be the Lipschitz-free space of $(M,o)$, the closed linear span of the evaluation functionals $\delta(x):f\mapsto f(x)$ in the dual of the space $\mathrm{Lip}_0(M)$ of real Lipschitz functions vanishing at $o$; write $\langle u,f\rangle$ for the pairing. For $j\in M$ let $c_j(u)=\langle u,\chi_j\rangle$, where $\chi_j$ is the indicator of $\{j\}$ if $j\ne o$ and $\chi_o=0$, and let $P_Su=\sum_{j\in S}c_j(u)\,\delta(j)$.
--
--   The *affine weights* of $u\in\mathcal F(M)$ are the numbers
--   $$\mu_u(j)=c_j(u)+[\,j=o\,]\Bigl(1-\sum_{k\in S}c_k(u)\Bigr),\qquad j\in S,$$
--   where $[\,j=o\,]$ is $1$ if $j=o$ and $0$ otherwise. Since $c_o=0$, they satisfy $\mu_u(j)=c_j(u)$ for $j\ne o$ and $\sum_{j\in S}\mu_u(j)=1$.
--
--   **Theorem.** Let $u\in\mathcal F(M)$ satisfy $P_Su=u$, and let $g:M\to\mathbb{R}$ satisfy $|g(x)-g(y)|\le C\,d(x,y)$ for all $x,y\in M$, where $C\ge0$. Let $g-g(o)\in\mathrm{Lip}_0(M)$ denote the function $x\mapsto g(x)-g(o)$. Then
--   $$
--   \sum_{j\in S}\mu_u(j)\,g(j)=\bigl\langle u,\ g-g(o)\bigr\rangle+g(o).
--   $$
--
--   For $u=\delta(x)$ with $x\in S$ the affine weights form the unit point mass at $x$, and both sides equal $g(x)$. In general the identity represents the affine functional $g\mapsto\langle u,g-g(o)\rangle+g(o)$ by a finite signed weight of total mass $1$ on $S$, so that estimates for an operator $T$ whose range lies in the span of $\{\delta(j):j\in S\}$ become inequalities about finitely many real numbers tested against Lipschitz functions.
--
--   **Formalization Note** The weights are `affineWeights o sep S ho u`, a function on the subtype of $S$, and the left-hand side is `pairing μ g`, the finite sum of $\mu(j)\,g(j)$. The centred function is `Lip0.center o g C hC hg`, which requires the Lipschitz bound with a constant $C\ge0$, and $\langle u,\cdot\rangle$ is `dualPairing o`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/AffineWeights.lean#L27-L43

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

theorem OAI.DiscreteFree.affineWeights_pairing (u : FreeSpace o)
    (hu : supportProjection o sep S u = u) (g : M → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ x y, |g x - g y| ≤ C * dist x y) :
    pairing (affineWeights o sep S ho u) (fun j : S => g j.val) =
      dualPairing o (Lip0.center o g C hC hg) u + g o := by sorry
