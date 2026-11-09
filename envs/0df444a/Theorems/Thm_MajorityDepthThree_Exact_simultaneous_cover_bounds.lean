-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_simultaneous_cover_bounds
-- name    : MajorityDepthThree.Exact.simultaneous_cover_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:28.312881+00:00
-- url     : https://prove2.me/theorems/fba22568-6642-4e9b-8b70-5e614966c0e4
-- title:
--   Theorem 5.15 — all four simultaneous upper bounds
-- statement:
--   Let $F$ be any valid monotone 3-CNF on $n$ ambient variables, with $p=\sqrt{3/2}$, $r=p/2$, $q=1/p$, $c_0=1$, $c_1=(2-q)^{-1}$, $c_2=c_1^2$, and $c_3=r$. Its covering minimum satisfies all four assertions:
--
--   $$C_F\le c_0p^n;\quad
--   \#\{\text{2-clauses}\}\ge1\Rightarrow C_F\le c_1p^n;\quad
--   \#\{\text{2-clauses}\}\ge2\Rightarrow C_F\le c_2p^n;\quad
--   \#\{\text{2-clauses}\}\ge3\Rightarrow C_F\le c_3p^n.$$
--
--   Counts refer to distinct clauses and require no disjointness. Width is at most three; unit and empty clauses, isolated variables and the empty ground set are included. The conclusion is the whole simultaneous theorem S1–S4, supplying the covering budgets needed by the counting bound.
--
--   Differences from the source:
--   - encoding: A finite ground set V and its subsets → Finite subsets V of a variable type, with finite families of subsets; reason: Every source instance has this representation; all assignments and ambient isolated variables are retained
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.16, Theorem 5.15 and preceding constants

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem simultaneous_cover_bounds {α : Type} [DecidableEq α] (V : Finset α)
    (F : CNF α) (hv : ValidCNF V F) (hm : Monotone F) (hw : Width 3 F) :
    coverValue (transversals V F) r q ≤ c₀ * p ^ V.card ∧
    (1 ≤ twoClauseCount F → coverValue (transversals V F) r q ≤ c₁ * p ^ V.card) ∧
    (2 ≤ twoClauseCount F → coverValue (transversals V F) r q ≤ c₂ * p ^ V.card) ∧
    (3 ≤ twoClauseCount F → coverValue (transversals V F) r q ≤ c₃ * p ^ V.card) := by sorry

end MajorityDepthThree.Exact
