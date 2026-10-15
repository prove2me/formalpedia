-- Prove2me | Theorems.Thm_OAI_DiscreteFree_ColorCounting_colored_roots_bound
-- name    : OAI.DiscreteFree.ColorCounting.colored_roots_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:10:06.180504+00:00
-- url     : https://prove2.me/theorems/4f4120ca-3c9a-42ce-9a3b-8ec414674991
-- title:
--   Union bound for coloured roots satisfying colour constraints along injective patterns
-- statement:
--   Let $X,W,I,S,C$ be finite sets; think of $X$ as vertices, $C$ as colours, $W$ as patterns and $S$ as constraint profiles. Let $f:X\times W\times I\to X$ be such that $i\mapsto f(x,w,i)$ is injective for every $x\in X$ and $w\in W$. For each $s\in S$ and $i\in I$ let $P(s,i)\subseteq C$ be a set of allowed colours, and let $H\in\mathbb{N}$ satisfy $|P(s,i)|\le H$ for all $s,i$. Consider the set of *bad coloured roots*
--   $$\mathcal B=\bigl\{(c,x)\in C^X\times X:\ \text{there are } w\in W,\ s\in S \text{ with } c\bigl(f(x,w,i)\bigr)\in P(s,i)\ \text{for all } i\in I\bigr\}.$$
--
--   **Theorem.**
--   $$
--   |\mathcal B|\cdot|C|^{|I|}\ \le\ |W|\cdot|S|\cdot H^{|I|}\cdot\bigl|C^X\times X\bigr| .
--   $$
--
--   Dividing by $|C|^{|I|}\,|C^X\times X|$: for a uniformly random colouring $c$ and a uniformly random root $x$, the probability that some pattern $w$ and some profile $s$ are satisfied is at most $|W|\,|S|\,(H/|C|)^{|I|}$. With $X$ the vertex set of a Cayley graph, $W$ the reduced words of length $n$, $f(x,w,i)$ the vertex reached after $i$ steps along $w$, and $S$ the paths of states, this bounds the proportion of coloured vertices from which a matched walk starts.
--
--   **Formalization Note** All sets are `Fintype`s; $\mathcal B$ is a subtype of `(X → C) × X`, the counts are `Fintype.card`, and the statement is multiplied out so that only natural numbers appear.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/ColorCounting.lean#L133-L151

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
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting

open OAI OAI.DiscreteFree OAI.DiscreteFree.ColorCounting
open scoped BigOperators ENNReal
open scoped BigOperators Classical

theorem OAI.DiscreteFree.ColorCounting.colored_roots_bound {X W I S C : Type*}
    [Fintype X] [Fintype W] [Fintype I] [Fintype S] [Fintype C]
    (f : X → W → I → X) (hf : ∀ x w, Function.Injective (f x w))
    (P : S → I → Finset C) (H : ℕ) (hH : ∀ s i, (P s i).card ≤ H) :
    Fintype.card {z : (X → C) × X // ∃ w s, ∀ i, z.1 (f z.2 w i) ∈ P s i} *
        Fintype.card C ^ Fintype.card I ≤
      Fintype.card W * Fintype.card S * H ^ Fintype.card I * Fintype.card ((X → C) × X) := by sorry
