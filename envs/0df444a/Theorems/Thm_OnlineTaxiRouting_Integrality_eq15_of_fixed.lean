-- Prove2me | Theorems.Thm_OnlineTaxiRouting_Integrality_eq15_of_fixed
-- name    : OnlineTaxiRouting.Integrality.eq15_of_fixed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:08.147418+00:00
-- url     : https://prove2.me/theorems/43200333-b299-43ea-8051-5dc9c05744e7
-- title:
--   §3.2, proof of Theorem 1, display (15), p. 13 — with fixed windows (12) forces t = t*, and (13) becomes (15)
-- statement:
--   Consider a taxi routing instance in which every customer has a fixed pick-up time, $t^{\min}_c = t^{\max}_c =: t^*_c$ for all $c \in \mathcal C$. Then for every point $(x, y, p, t)$:
--
--   1. the window constraint (12), $t^{\min}_c \le t_c \le t^{\max}_c$ for all $c$, holds if and only if $t = t^*$;
--   2. if $t = t^*$, then for every pair of customers $c, c'$ the time constraint (13) holds if and only if
--   $$\big(T_{c',c} - (t^*_c - t^*_{c'})\big)\, x_{c',c} \le 0. \qquad (15)$$
--
--   This is the first step of the proof of Theorem 1: once the pick-up times are fixed, the Big-M constraint (13) only constrains the single variable $x_{c',c}$.
--
--   **Formalization Note** The standing acyclicity assumption of §2.1 is not needed and is omitted, which makes the statement stronger.
-- source:
--   Bertsimas–Jaillet–Martin, accepted manuscript (March 2018), §3.2, proof of Theorem 1, display (15), p. 13

import Mathlib
import Definitions.Def_OnlineTaxiRouting_Integrality_Setting

namespace OnlineTaxiRouting.Integrality

theorem eq15_of_fixed {C K : Type*} (I : Instance C K)
    (hfix : ∀ c, I.tmin c = I.tmax c) (v : Var C K) :
    ((∀ c, I.tmin c ≤ v.2.2.2 c ∧ v.2.2.2 c ≤ I.tmax c) ↔ v.2.2.2 = I.tmin) ∧
    (v.2.2.2 = I.tmin → ∀ c c',
      ((I.tmin c - I.tmax c') + (I.T c' c - (I.tmin c - I.tmax c')) * v.1 c' c
          ≤ v.2.2.2 c - v.2.2.2 c' ↔
        (I.T c' c - (I.tmin c - I.tmin c')) * v.1 c' c ≤ 0)) := by sorry

end OnlineTaxiRouting.Integrality
