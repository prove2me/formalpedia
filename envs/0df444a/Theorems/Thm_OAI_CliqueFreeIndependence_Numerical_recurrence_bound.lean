-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_recurrence_bound
-- name    : OAI.CliqueFreeIndependence.Numerical.recurrence_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:15:11.870772+00:00
-- url     : https://prove2.me/theorems/76e4ca87-da60-4345-bf44-8431439791d4
-- title:
--   Absorbing small losses in a recursive bound: from $(1-\varepsilon)t-sm\le B(2-2q)m$ to $t\le B(2-q)m$
-- statement:
--   Let $B,q,\varepsilon,t,m,s$ be real numbers such that $B\ge1$, $0\le q\le1$, $0\le\varepsilon\le q/4$, $t\ge0$, $m\ge0$ and $s\le q/2$. If
--
--   $$
--   (1-\varepsilon)\,t-s\,m\le B(2-2q)\,m,
--   $$
--
--   then
--
--   $$
--   t\le B(2-q)\,m.
--   $$
--
--   The lemma says that a bound for $t$ in terms of $m$ which suffers a multiplicative loss $1-\varepsilon$ and an additive loss $sm$ can still be closed with the slightly weaker coefficient $B(2-q)$ instead of $B(2-2q)$, provided both losses are small compared with $q$. In the multi-scale induction that bounds the weighted triangle mass of a graph by a multiple of its edge mass, $t$ is a triangle mass, $m$ an edge mass, and $q=2^{-(n+1)}$; the lemma passes from the coefficient $B(2-2^{-n})$ of one stage to $B(2-2^{-(n+1)})$ at the next, so all coefficients stay below $2B$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Numerical.lean#L180-L196

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.Numerical
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Filter

theorem OAI.CliqueFreeIndependence.Numerical.recurrence_bound {B q ε t m s : ℝ}
    (hB : 1 ≤ B) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (_hε0 : 0 ≤ ε) (hε : ε ≤ q/4) (_ht : 0 ≤ t) (hm : 0 ≤ m)
    (hs : s ≤ q/2)
    (hstep : (1-ε)*t - s*m ≤ B*(2-2*q)*m) :
    t ≤ B*(2-q)*m := by sorry
