-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MM1RationalAtZeroV1
-- name    : Kyprianou.Ch04.exercise46MM1RationalAtZeroV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:43:46.541797+00:00
-- url     : https://prove2.me/theorems/98553b35-76ff-5c8f-9d29-cb15d2f5b7ab
-- title:
--   M/M/1 regular rational function limit
-- statement:
--   M/M/1 regular rational function limit
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MM1RationalAtZeroV1
    (lambda mu beta : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hbeta : 0 < beta) :
    Tendsto (fun phi : Real =>
      (phi+mu-lambda)*(mu+beta) /
        ((mu+beta)*(mu+phi)-lambda*mu))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((1-lambda/mu)*(1+lambda/(mu-lambda+beta)))) := by
  sorry
