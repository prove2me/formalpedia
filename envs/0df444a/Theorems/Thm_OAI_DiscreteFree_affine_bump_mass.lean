-- Prove2me | Theorems.Thm_OAI_DiscreteFree_affine_bump_mass
-- name    : OAI.DiscreteFree.affine_bump_mass
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:04:56.935376+00:00
-- url     : https://prove2.me/theorems/4b87be9f-4d98-418d-afba-2074f506bedc
-- title:
--   An almost fixed nearby anchor forces almost full bump mass in the affine weights of $T\delta(x)$
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$ such that $d(x,y)\ge1$ whenever $x\ne y$, let $N$ be a metric space, and let $S\subseteq M$ be finite with $o\in S$. Let $\mathcal F(M)$ be the Lipschitz-free space of $(M,o)$, the closed linear span of the evaluation functionals $\delta(x):f\mapsto f(x)$ in the dual of the space $\mathrm{Lip}_0(M)$ of real Lipschitz functions vanishing at $o$ (normed by the best Lipschitz constant). For $j\in M$ let $c_j(u)=\langle u,\chi_j\rangle$, with $\chi_j$ the indicator of $\{j\}$ if $j\ne o$ and $\chi_o=0$; let $P_Su=\sum_{j\in S}c_j(u)\,\delta(j)$; and let $\mu_u(j)=c_j(u)+[\,j=o\,]\bigl(1-\sum_{k\in S}c_k(u)\bigr)$, $j\in S$, be the affine weights of $u$, where $[\,j=o\,]$ is $1$ if $j=o$ and $0$ otherwise.
--
--   Let $T$ be a bounded linear operator on $\mathcal F(M)$ with $P_S(Tu)=Tu$ for all $u$, let $h:M\to N$ be $1$-Lipschitz, and let $x,a\in M$ with $h(a)=h(x)$. Let $L,K,p,R$ be real numbers with $L\ge0$, $K>0$, $p\ge0$, $\|T\|\le 2p$, $d(x,a)\le R$ and $\|T\delta(a)-\delta(a)\|<1$. Consider the bump
--   $$b(t)=L\cdot\max\Bigl(1-\frac{d\bigl(h(x),h(t)\bigr)}{K},\,0\Bigr),\qquad t\in M .$$
--
--   **Theorem.** Under these assumptions
--   $$
--   \sum_{j\in S}\mu_{T\delta(x)}(j)\,b(j)\ \ge\ L-\frac{L}{K}\,(2pR+1).
--   $$
--
--   The bump attains its maximal value $L$ at all points whose $h$-image equals $h(x)$. The theorem says that if a point $a$ near $x$ with the same $h$-value is moved by $T$ by less than $1$, then the affine weights of $T\delta(x)$ give almost full mass $L$ to the bump, with a loss proportional to $L/K$. In the block obstruction $h$ is the label map, $a$ is the anchor attached to the vertex $x$ at distance $R$, and the parameters are chosen so that the right-hand side is at least $3L/4$.
--
--   **Formalization Note** The bump is `labelBump h (h x) L K`, the weights are `affineWeights o sep S ho (T (delta o x))`, and the left-hand side is `pairing` of the weights with the bump restricted to $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/LabelBumps.lean#L73-L107

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
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps

open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

theorem OAI.DiscreteFree.affine_bump_mass (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)
    (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (h : M → N) (hh : LipschitzWith 1 h) (x a : M) (ha : h a = h x)
    (L K p R : ℝ) (hL : 0 ≤ L) (hK : 0 < K) (hp : 0 ≤ p)
    (hn : ‖T‖ ≤ 2*p) (hR : dist x a ≤ R) (he : ‖T (delta o a) - delta o a‖ < 1) :
    L - (L/K)*(2*p*R+1) ≤
      pairing (affineWeights o sep S ho (T (delta o x)))
        (fun j : S => labelBump h (h x) L K j.val) := by sorry
