-- Prove2me | Theorems.Thm_OAI_ForestSpace_simultaneous_cut_bound
-- name    : OAI.ForestSpace.simultaneous_cut_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:14:12.260396+00:00
-- url     : https://prove2.me/theorems/280d5c42-5029-49bf-9a6a-7e64db36fcdb
-- title:
--   Charging all suffix cuts to a single disjoint segment test of the head function
-- statement:
--   Let $V$ be a finite partially ordered set. A *segment* is a finite chain $S\subseteq V$ that is order-convex; for $u:V\to\mathbb{R}$ and finite $S\subseteq V$ put $u(S)=\sum_{v\in S}u(v)$, and write $\|u\|_{\mathrm{seg}}^2\le C$ if $\sum_i u(S_i)^2\le C$ for every finite family $(S_i)$ of pairwise disjoint segments.
--
--   **Theorem.** Let $H\subseteq V$ be any subset and let $f:V\to\mathbb{R}$ vanish outside $H$ with $\|f\|_{\mathrm{seg}}^2\le1$. Let $I$ be a finite index set, let $(S_i)_{i\in I}$ be pairwise disjoint finite subsets of $V$, and let $(L_i)_{i\in I}$ be finite sets with $L_i\subseteq S_i\cap H$ such that $L_i$ and $(S_i\cap H)\setminus L_i$ are segments for every $i$. Then
--   $$
--   \sum_{i\in I}\Bigl[\bigl(f(S_i)-f(L_i)\bigr)^2+f(L_i)^2\Bigr]\le1 .
--   $$
--
--   Neither the sets $S_i$ are required to be segments nor $H$ to be a lower set; only the pieces $L_i$ and $(S_i\cap H)\setminus L_i$ must be segments. In the paired-correction estimate the $L_i$ are the suffix cuts chosen segment by segment, and this inequality bounds their total cost by the single constant $1$, which becomes the leading term of the bound $1+12s^2$.
--
--   **Formalization Note** The finite family is indexed by a type `ι` with a `Fintype` instance; $S_i\cap H$ is the filter of $S_i$ by membership in $H$, and "vanishes outside $H$" is `SupportedOn f H`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Paired.lean#L115-L154

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [PartialOrder V]

omit [Fintype V] [PartialOrder V] in
theorem OAI.ForestSpace.simultaneous_cut_bound [Fintype V] [PartialOrder V] {H : Set V} {f : V → ℝ}
    (hf : SupportedOn f H) (hf₁ : TestBound f 1)
    {ι : Type} [Fintype ι] (S L : ι → Finset V)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hL : ∀ i, L i ⊆ (S i).filter (· ∈ H))
    (hseg : ∀ i, IsSegment (L i))
    (hdiff : ∀ i, IsSegment ((S i).filter (· ∈ H) \ L i)) :
    (∑ i, ((segSum f (S i) - segSum f (L i)) ^ 2 + segSum f (L i) ^ 2)) ≤ 1 := by sorry
