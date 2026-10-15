-- Prove2me | Theorems.Thm_OAI_DiscreteFree_GraphProducer_prefixes_injective
-- name    : OAI.DiscreteFree.GraphProducer.prefixes_injective
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:07:33.931496+00:00
-- url     : https://prove2.me/theorems/cdfc7625-2287-4fdd-9988-f51d3d377c73
-- title:
--   Reduced words of length at most $N$ trace injective walks in a finite permutation model of the free group
-- statement:
--   Let $A$ be a finite alphabet and $F(A)$ the free group on $A$; for $g\in F(A)$ let $|g|$ be the length of its reduced word. For $N\in\mathbb{N}$ let $B_N=\{g\in F(A):\ |g|\le N\}$, a finite set, and let $\mathrm{Sym}(B_N)$ be its group of permutations. For each $a\in A$ fix a permutation $\sigma_a$ of $B_N$ such that
--   $$\sigma_a(g)=a\,g\qquad\text{whenever } g\in B_N \text{ and } |a\,g|\le N$$
--   (the partial injection $g\mapsto ag$ between subsets of $B_N$ extends to a permutation), and let $\rho_N:F(A)\to\mathrm{Sym}(B_N)$ be the group homomorphism with $\rho_N(a)=\sigma_a$.
--
--   **Theorem.** Let $s_1s_2\cdots s_m$ be a reduced word in the letters $a^{\pm1}$, $a\in A$ (no letter is immediately followed by its inverse), with $m\le N$, and let $\pi\in\mathrm{Sym}(B_N)$. Then the $m+1$ permutations
--   $$
--   \pi\,\rho_N(s_1s_2\cdots s_i),\qquad i=0,1,\dots,m,
--   $$
--   are pairwise distinct (for $i=0$ the product $s_1\cdots s_i$ is the identity).
--
--   Equivalently, in the Cayley graph of the finite group $\mathrm{Sym}(B_N)$ with respect to the generators $\sigma_a$, the walk from any vertex $\pi$ along a reduced word of length at most $N$ never revisits a vertex; in particular no reduced word of positive length at most $N$ gives a closed walk. This is the finite large-girth input of the construction: the vertices visited by a reduced walk are distinct, so the colours that a uniformly random colouring assigns to them are independent.
--
--   **Formalization Note** Words are lists over `A × Bool`, with `(a, true)` standing for $a$ and `(a, false)` for $a^{-1}$; reducedness is `FreeGroup.IsReduced`, $|g|$ is `FreeGroup.norm`, $B_N$ is `WordBall A N`, $\sigma_a$ is `ballPerm A N a` (chosen with `Equiv.Perm.exists_extending_pair`) and $\rho_N$ is `ballRep A N`. The statement asserts injectivity on `Fin (m+1)` of $i\mapsto\pi\,\rho_N(\mathrm{mk}(\ell_{\le i}))$, where $\ell_{\le i}$ is the prefix of length $i$ and the product of permutations is composition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/FiniteQuotients.lean#L130-L147

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
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients

open OAI OAI.DiscreteFree OAI.DiscreteFree.GraphProducer
open scoped BigOperators ENNReal
variable (A : Type*) [Finite A] [DecidableEq A]

theorem OAI.DiscreteFree.GraphProducer.prefixes_injective (N : ℕ) (l : List (A × Bool))
    (hl : FreeGroup.IsReduced l) (hlen : l.length ≤ N)
    (x : Equiv.Perm (WordBall A N)) :
    Function.Injective (fun i : Fin (l.length + 1) =>
      x * ballRep A N (FreeGroup.mk (l.take i.val))) := by sorry
