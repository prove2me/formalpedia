-- Prove2me | Theorems.Thm_IntMul_HvdH_bilinear_error_propagation
-- name    : IntMul.HvdH.bilinear_error_propagation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:32:09.874953+00:00
-- url     : https://prove2.me/theorems/05a0a856-db82-4d81-9b12-b850068ca55e
-- title:
--   Error propagation through an approximate bilinear map (Lemma 2.9)
-- statement:
--   Let $A:U\times V\to W$ be a continuous $\mathbb C$-bilinear map with $\|A\|\le1$ and let $\tilde A$ be any function $U\times V\to W$. Let $\|u\|\le1$, $\|\tilde v\|\le1$, $\|\tilde A(\tilde u,\tilde v)-A(\tilde u,\tilde v)\|\le\varepsilon_A$, $\|\tilde u-u\|\le\varepsilon_u$ and $\|\tilde v-v\|\le\varepsilon_v$. Then
--   $$\|\tilde A(\tilde u,\tilde v)-A(u,v)\|\le\varepsilon_A+\varepsilon_u+\varepsilon_v.$$
--   This is Lemma 2.9 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.6

import Mathlib

namespace IntMul.HvdH
theorem bilinear_error_propagation {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (A : U →L[ℂ] V →L[ℂ] W) (hA : ‖A‖ ≤ 1) (Aa : U → V → W)
    (u ut : U) (v vt : V) (eA eu ev : ℝ) (hu1 : ‖u‖ ≤ 1) (hvt1 : ‖vt‖ ≤ 1)
    (hAa : ‖Aa ut vt - A ut vt‖ ≤ eA) (hu : ‖ut - u‖ ≤ eu) (hv : ‖vt - v‖ ≤ ev) :
    ‖Aa ut vt - A u v‖ ≤ eA + eu + ev := by sorry
end IntMul.HvdH
