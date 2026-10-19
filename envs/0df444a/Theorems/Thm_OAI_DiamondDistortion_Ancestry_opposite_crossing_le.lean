-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_opposite_crossing_le
-- name    : OAI.DiamondDistortion.Ancestry.opposite_crossing_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:52:26.673429+00:00
-- url     : https://prove2.me/theorems/a8028eb6-fe02-41bc-a3e8-9720c549420f
-- title:
--   Opposite-crossing estimate at the gates of an ancestral head for two segment families
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$. A *gate* of $H$ is a vertex $g\notin H$ all of whose strict ancestors lie in $H$. For a segment family $\mathcal F=(S_1,\dots,S_n)$, a finitely supported $p$ and $g\in V$, the *boundary coefficient* is $\beta_{\mathcal F}(g)=\sum_{i:\,g\in S_i}p(S_i)$; by disjointness it equals $p(S_i)$ for the unique member $S_i$ containing $g$, and $0$ if no member contains $g$.
--
--   Let $\kappa$ be a finite set, let $H\subseteq V$ be ancestral, and let $p$ be finitely supported with $p(v)=0$ for all $v\notin H$. Let $\mathcal F=(S_1,\dots,S_n)$ and $\mathcal G=(T_1,\dots,T_m)$ be segment families, and let $g:\kappa\to V$ be injective such that every $g_a$ is a gate of $H$. Then
--
--   $$
--   \sum_{a\in\kappa}\Big(|\beta_{\mathcal F}(g_a)|\,|\beta_{\mathcal G}(g_a)|-\beta_{\mathcal F}(g_a)\,\beta_{\mathcal G}(g_a)\Big)\le\Big(\|p\|_{\mathrm{seg}}^2-\sum_{i=1}^{n}p(S_i)^2\Big)+\Big(\|p\|_{\mathrm{seg}}^2-\sum_{j=1}^{m}p(T_j)^2\Big).
--   $$
--
--   A summand vanishes when the two boundary coefficients at $g_a$ have the same sign or one of them is zero, and equals $2|\beta_{\mathcal F}(g_a)\beta_{\mathcal G}(g_a)|$ when they have opposite signs. So the left side measures the total opposite-sign crossing of the two families at the chosen gates, and the estimate charges it to the slacks of the two families. Because no sign condition appears, the inequality can be averaged directly over pairs of families drawn from finite laws, which is how it enters the pooled tail estimates for the dual of the segment-norm space.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance, $H$ is a `Set`, the gates are an embedding `κ ↪ ι` with `A.Gate H (gate a)` for all `a`, $\beta_{\mathcal F}$ is `A.boundaryCoeff F p`, and $\|p\|_{\mathrm{seg}}$ is `A.segments.primalSeminorm p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L398-L462

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
universe u v
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
variable {ι : Type*} [A : Ancestry ι]

theorem OAI.DiamondDistortion.Ancestry.opposite_crossing_le {κ : Type*} [Fintype κ]
    {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (gate : κ ↪ ι) (hgate : ∀ a, A.Gate H (gate a)) :
    (∑ a, (|A.boundaryCoeff F p (gate a)| * |A.boundaryCoeff G p (gate a)| -
      A.boundaryCoeff F p (gate a) * A.boundaryCoeff G p (gate a))) ≤
      ((A.segments.primalSeminorm p) ^ 2 - ∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      ((A.segments.primalSeminorm p) ^ 2 - ∑ j, (∑ v ∈ G.seg j, p v) ^ 2) := by sorry
