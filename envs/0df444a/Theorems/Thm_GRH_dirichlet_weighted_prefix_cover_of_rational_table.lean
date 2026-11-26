-- Prove2me | Theorems.Thm_GRH_dirichlet_weighted_prefix_cover_of_rational_table
-- name    : GRH.dirichlet_weighted_prefix_cover_of_rational_table
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T16:15:50.933814+00:00
-- url     : https://prove2.me/theorems/958fed94-3291-447e-a1b6-cfb5dcce2d97
-- title:
--   Integer power brackets certify a weighted Dirichlet prefix bound
-- statement:
--   A finite integer table bounds the real weighted-prefix error. At index $n$, the adjacent integers $u_n-1,u_n$ enclose $D n^{-p/t}$ after checking two integer power inequalities. If $v$ times the resulting integer mass is strictly below $wD$, the geometric rectangle conditions at exponent $p/t$ and multiplier $v/w$ give a weighted-prefix cover.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletPrefix

open GRH.DirichletPrefix

theorem GRH.dirichlet_weighted_prefix_cover_of_rational_table (d Q M R D p t v w : ℕ) (u : ℕ → ℕ) (a b H : ℝ)
    (hq : 2<Q) (hd : d ∣ Q) (hD : 0<D) (hp : 0<p) (ht : 0<t) (hw : 0<w)
    (hx : (p:ℝ)/t ≤ a) (hrect : b^2+H^2 ≤ (((v:ℝ)/w)*((p:ℝ)/t))^2)
    (hR : ∀ r : Fin Q, weightAt Q r.val ≤ R)
    (htable : Table M D p t u) (hstrict : v*mass Q M R u < w*D) : Covers d a b H := by sorry
