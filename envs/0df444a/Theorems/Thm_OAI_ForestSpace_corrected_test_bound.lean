-- Prove2me | Theorems.Thm_OAI_ForestSpace_corrected_test_bound
-- name    : OAI.ForestSpace.corrected_test_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:15:17.239336+00:00
-- url     : https://prove2.me/theorems/854eeee9-9559-4cbf-a420-a5a0222dae3e
-- title:
--   The gate-corrected test $f+sT$ has squared segment norm at most $1+12s^2$
-- statement:
--   Let $V$ be a finite partially ordered set that is a *forest*: whenever $a\le c$ and $b\le c$, the elements $a$ and $b$ are comparable. Let $H\subseteq V$ be a lower set; a *gate* of $H$ is an element $g\notin H$ such that every $v<g$ lies in $H$. Segments, segment sums $u(S)=\sum_{v\in S}u(v)$ and the squared segment norm $\|u\|_{\mathrm{seg}}^2$ (the supremum of $\sum_i u(S_i)^2$ over finite families of pairwise disjoint segments) are as usual, and $[a,g)=\{v:\ a\le v<g\}$, $[g,w]=\{v:\ g\le v\le w\}$.
--
--   Let $f,k:V\to\mathbb{R}$ with $f(v)=0$ for $v\notin H$ and $k(v)=0$ for $v\in H$, and let $s,\tau\in\mathbb{R}$. The following quantities are used, for $g\in V$.
--   - The *mass* of $k$ at $g$: $m(g)=\max_{w\in V}\bigl|k([g,w])\bigr|$.
--   - The *selected head* at $g$: $L_g=[a^*_g,g)$, where $a^*_g$ is a maximal element (fixed by a choice function) of the set of *large starts* $\{a\in V:\ a<g,\ 2s\,m(g)\le|f([a,g))|\}$; if there is no large start, $L_g=\varnothing$.
--   - The *gate sign* $\sigma(g)=1$ if $f(L_g)<0$ and $\sigma(g)=-1$ otherwise.
--   - The *gate correction* $c(v)=\sigma(v)\,m(v)$ if $v$ is a gate of $H$, and $c(v)=0$ otherwise; the *corrected tail* is $T=c+\tau k$.
--
--   **Theorem.** Assume $\|f\|_{\mathrm{seg}}^2\le1$, $\|k\|_{\mathrm{seg}}^2\le1$, $s\ge0$ and $|\tau|\le1$. Then
--   $$
--   \|f+s\,T\|_{\mathrm{seg}}^2\le1+12s^2,
--   $$
--   that is, $\sum_{i\in I}\bigl(f(S_i)+s\,T(S_i)\bigr)^2\le1+12s^2$ for every finite family $(S_i)_{i\in I}$ of pairwise disjoint segments.
--
--   The gate signs $\sigma$, and hence the correction $c$, depend on $f$, $k$ and $s$ but not on $\tau$. Applying the theorem with $\tau=1$ and $\tau=-1$ therefore gives one correction $c$ for which both $f+s(c+k)$ and $f+s(c-k)$ have squared segment norm at most $1+12s^2$; this "for either sign" form is what makes the correction cancel when the two tests are averaged in the dual estimate.
--
--   **Formalization Note** The squared-norm bound is the proposition `TestBound (f + s • correctedTail H f k s τ) (1 + 12 * s ^ 2)`; see the previous items for the Lean names of the mass, gate signs and corrected tail.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Paired.lean#L156-L173

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

theorem OAI.ForestSpace.corrected_test_bound (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {f k : V → ℝ} (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hf₁ : TestBound f 1) (hk₁ : TestBound k 1)
    {s τ : ℝ} (hs : 0 ≤ s) (hτ : |τ| ≤ 1) :
    TestBound (f + s • correctedTail H f k s τ) (1 + 12 * s ^ 2) := by sorry
