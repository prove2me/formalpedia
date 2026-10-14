-- Prove2me | Theorems.Thm_IntMul_HvdH_error_composition
-- name    : IntMul.HvdH.error_composition
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:32:23.057993+00:00
-- url     : https://prove2.me/theorems/c995f679-244d-43e9-bc3d-4fd07fe83656
-- title:
--   Error of a composition of approximate linear maps (Corollary 2.8)
-- statement:
--   Let $A:U\to V$ and $B:V\to W$ be continuous $\mathbb C$-linear maps with $\|B\|\le1$. Let $\tilde A:U\to V$ map a set $S$ into a set $T$ with $\|\tilde Au-Au\|\le\varepsilon_A$ on $S$, and let $\tilde B:V\to W$ satisfy $\|\tilde Bv-Bv\|\le\varepsilon_B$ on $T$. Then for all $u\in S$,
--   $$\|\tilde B\tilde Au-BAu\|\le\varepsilon_B+\varepsilon_A.$$
--   This is Corollary 2.8 of Harvey–van der Hoeven, with $S,T$ the fixed-point unit balls.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.6

import Mathlib

namespace IntMul.HvdH
theorem error_composition {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (A : U →L[ℂ] V) (B : V →L[ℂ] W) (hB : ‖B‖ ≤ 1)
    (Aa : U → V) (Bb : V → W) (S : Set U) (T : Set V) (eA eB : ℝ)
    (hAaT : ∀ u ∈ S, Aa u ∈ T) (hAa : ∀ u ∈ S, ‖Aa u - A u‖ ≤ eA)
    (hBb : ∀ v ∈ T, ‖Bb v - B v‖ ≤ eB) :
    ∀ u ∈ S, ‖Bb (Aa u) - B (A u)‖ ≤ eB + eA := by sorry
end IntMul.HvdH
