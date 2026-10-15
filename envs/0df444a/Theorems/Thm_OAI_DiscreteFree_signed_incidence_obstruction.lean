-- Prove2me | Theorems.Thm_OAI_DiscreteFree_signed_incidence_obstruction
-- name    : OAI.DiscreteFree.signed_incidence_obstruction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:55:49.484841+00:00
-- url     : https://prove2.me/theorems/bcf2597f-d764-4ec9-8331-6a635eca2fcc
-- title:
--   Incidence averaging obstruction: signed weights of small total variation cannot charge every reversed edge pair by $13/20$
-- statement:
--   Let $X$, $D$ and $S$ be finite sets with $X\neq\varnothing$ and $D\neq\varnothing$. For a function $\mu:S\to\mathbb{R}$ write $\|\mu\|_1=\sum_{j\in S}|\mu(j)|$ for its total variation and, for $E\subseteq S$, $\operatorname{var}_\mu(E)=\sum_{j\in E}|\mu(j)|$ for its variation on $E$.
--
--   Suppose we are given signed weights $\mu_x:S\to\mathbb{R}$ for $x\in X$, sets $E(x,e)\subseteq S$ for $(x,e)\in X\times D$, a set $B\subseteq X$ of *bad* elements, a permutation $\rho$ of $X\times D$, and real numbers $p>0$ and $V\ge0$ such that
--
--   1. $\|\mu_x\|_1\le V$ for every $x\in X$;
--   2. for every $x\notin B$ the sets $E(x,e)$, $e\in D$, are pairwise disjoint;
--   3. $20V<|D|$;
--   4. $20V\,|B|<|X|$;
--   5. for every pair $(x,e)\in X\times D$, writing $\rho(x,e)=(x',e')$,
--   $$
--   \frac{3\cdot(10p)}{2}-2\cdot(10p)\Bigl(\operatorname{var}_{\mu_x}\bigl(E(x,e)\bigr)+\operatorname{var}_{\mu_{x'}}\bigl(E(x',e')\bigr)\Bigr)\le 2p .
--   $$
--
--   Then these assumptions are contradictory: no such data exist.
--
--   Since $p>0$, condition 5 says exactly that $\operatorname{var}_{\mu_x}(E(x,e))+\operatorname{var}_{\mu_{x'}}(E(x',e'))\ge 13/20$ for every pair $(x,e)$. The theorem is the final counting step of a finite-rank obstruction in Lipschitz-free spaces. There $X$ is the vertex set of a finite graph whose oriented edges are the pairs $(x,e)$ with $e$ a port, $\rho$ reverses oriented edges, the $\mu_x$ are signed weights attached to the vertices, and condition 5 is what a Lipschitz test function along each edge produces at the scale $L=10p$. The theorem shows that such per-edge lower bounds cannot hold simultaneously when the weights have total variation much smaller than the degree and only few vertices have overlapping exceptional sets.
--
--   **Formalization Note** The sets are `Fintype`s with `Nonempty X` and `Nonempty D`, $B$ is a `Finset X`, $\rho$ is an equivalence `(X × D) ≃ (X × D)`, and the cardinalities $|D|$, $|X|$, $|B|$ are cast to real numbers. Total variation and variation on a set are `totalVariation` and `variationOn`; disjointness is stated as: if $j\in E(x,e)$ and $j\in E(x,f)$ then $e=f$. The hypothesis $V\ge0$ is part of the statement, and the conclusion is `False`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/SignedTests.lean#L207-L263

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

open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
variable {X D S : Type*} [Fintype X] [Fintype D] [Fintype S]

theorem OAI.DiscreteFree.signed_incidence_obstruction [Nonempty X] [Nonempty D]
    (μ : X → S → ℝ) (E : X → D → Set S) (bad : Finset X)
    (rev : (X × D) ≃ (X × D)) (p V : ℝ)
    (hp : 0 < p) (hV : 0 ≤ V)
    (hTV : ∀ x, totalVariation (μ x) ≤ V)
    (hgood : ∀ x, x ∉ bad → ∀ j e f, j ∈ E x e → j ∈ E x f → e = f)
    (hdegree : 20 * V < (Fintype.card D : ℝ))
    (hbad : 20 * V * (bad.card : ℝ) < (Fintype.card X : ℝ))
    (hedge : ∀ e : X × D,
      3 * (10 * p) / 2 - 2 * (10 * p) *
        (variationOn (μ e.1) (E e.1 e.2) +
         variationOn (μ (rev e).1) (E (rev e).1 (rev e).2)) ≤ 2 * p) : False := by sorry
