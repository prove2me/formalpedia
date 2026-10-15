-- Prove2me | Theorems.Thm_OAI_ForestSpace_segment_cut
-- name    : OAI.ForestSpace.segment_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:13:09.074387+00:00
-- url     : https://prove2.me/theorems/e308db93-3cad-436d-a50d-26e537e4160b
-- title:
--   Local suffix cut for the gate-corrected test on a single segment
-- statement:
--   Let $V$ be a finite partially ordered set that is a *forest*: whenever $a\le c$ and $b\le c$, the elements $a$ and $b$ are comparable. Let $H\subseteq V$ be a lower set; a *gate* of $H$ is an element $g\notin H$ such that every $v<g$ lies in $H$. Segments, segment sums $u(S)=\sum_{v\in S}u(v)$ and the squared segment norm $\|u\|_{\mathrm{seg}}^2$ (the supremum of $\sum_i u(S_i)^2$ over finite families of pairwise disjoint segments) are as usual, and $[a,g)=\{v:\ a\le v<g\}$, $[g,w]=\{v:\ g\le v\le w\}$.
--
--   Let $f,k:V\to\mathbb{R}$ with $f(v)=0$ for $v\notin H$ and $k(v)=0$ for $v\in H$, and let $s,\tau\in\mathbb{R}$. The following quantities are used, for $g\in V$.
--   - The *mass* of $k$ at $g$: $m(g)=\max_{w\in V}\bigl|k([g,w])\bigr|$.
--   - The *selected head* at $g$: $L_g=[a^*_g,g)$, where $a^*_g$ is a maximal element (fixed by a choice function) of the set of *large starts* $\{a\in V:\ a<g,\ 2s\,m(g)\le|f([a,g))|\}$; if there is no large start, $L_g=\varnothing$.
--   - The *gate sign* $\sigma(g)=1$ if $f(L_g)<0$ and $\sigma(g)=-1$ otherwise.
--   - The *gate correction* $c(v)=\sigma(v)\,m(v)$ if $v$ is a gate of $H$, and $c(v)=0$ otherwise; the *corrected tail* is $T=c+\tau k$.
--   - The *gate weight* $q(v)=m(v)^2$ if $v$ is a gate of $H$, and $q(v)=0$ otherwise.
--
--   **Theorem.** Assume $s\ge0$ and $|\tau|\le1$. For every segment $S$ there is a set $L\subseteq S\cap H$ such that $L$ and $(S\cap H)\setminus L$ are segments and
--   $$
--   \bigl(f(S)+s\,T(S)\bigr)^2\le\bigl(f(S)-f(L)\bigr)^2+f(L)^2+8s^2\sum_{v\in S}q(v)+s^2\,T(S)^2 .
--   $$
--
--   This is the one-segment step of the paired-correction estimate. The cross term $2s\,f(S)\,T(S)$ is either harmless, or paid for by a gate charge, or absorbed by splitting the head $S\cap H$ into the two disjoint segments $L$ and $(S\cap H)\setminus L$ (in that case $L$ is the selected head at the gate of $S$). Summing over a disjoint family of segments, the first two terms are controlled by one test of $f$, the gate charges by one test of $k$, and the last term by the segment norm of $T$, which gives the bound $1+12s^2$ for $\|f+sT\|_{\mathrm{seg}}^2$.
--
--   **Formalization Note** In Lean the mass is `mass k g` (a `Finset.sup'` over the finite type), $q$ is `gateWeight H k`, $L_g$ is `selectedHead f k s g` (the maximal start is chosen with `Classical.choose`), $\sigma$ is `gateSigns f k s` with the convention `oppositeSign r = if r < 0 then 1 else -1`, and $T$ is `correctedTail H f k s τ`. The support conditions are `SupportedOn f H` and `SupportedOn k Hᶜ`, and the forest condition is `ForestOrder V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Paired.lean#L64-L113

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

theorem OAI.ForestSpace.segment_cut (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {f k : V → ℝ} (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    {s τ : ℝ} (hs : 0 ≤ s) (hτ : |τ| ≤ 1)
    {S : Finset V} (hS : IsSegment S) :
    ∃ L : Finset V, L ⊆ S.filter (· ∈ H) ∧ IsSegment L ∧
      IsSegment (S.filter (· ∈ H) \ L) ∧
      (segSum f S + s * segSum (correctedTail H f k s τ) S) ^ 2 ≤
        (segSum f S - segSum f L) ^ 2 + segSum f L ^ 2 +
        8 * s ^ 2 * (∑ v ∈ S, gateWeight H k v) +
        s ^ 2 * segSum (correctedTail H f k s τ) S ^ 2 := by sorry
