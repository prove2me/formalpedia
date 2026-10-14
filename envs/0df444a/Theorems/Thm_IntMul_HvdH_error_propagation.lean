-- Prove2me | Theorems.Thm_IntMul_HvdH_error_propagation
-- name    : IntMul.HvdH.error_propagation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:32:09.816035+00:00
-- url     : https://prove2.me/theorems/e7b42b42-0121-4fd1-8cca-bc5d9b2a360e
-- title:
--   Error propagation through an approximate linear map (Lemma 2.7)
-- statement:
--   Let $A:V\to W$ be a continuous $\mathbb C$-linear map between normed spaces with $\|A\|\le1$, and let $\tilde A:V\to W$ be any function. If $\|\tilde A\tilde v-A\tilde v\|\le\varepsilon_A$ and $\|\tilde v-v\|\le\varepsilon_v$, then
--   $$\|\tilde A\tilde v-Av\|\le\varepsilon_A+\varepsilon_v.$$
--   This is Lemma 2.7 of Harvey–van der Hoeven (errors measured in units of $2^{-p}$ there).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.6

import Mathlib

namespace IntMul.HvdH
theorem error_propagation {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (A : V →L[ℂ] W) (hA : ‖A‖ ≤ 1) (Aa : V → W) (v vt : V) (eA ev : ℝ)
    (hAa : ‖Aa vt - A vt‖ ≤ eA) (hv : ‖vt - v‖ ≤ ev) : ‖Aa vt - A v‖ ≤ eA + ev := by sorry
end IntMul.HvdH
