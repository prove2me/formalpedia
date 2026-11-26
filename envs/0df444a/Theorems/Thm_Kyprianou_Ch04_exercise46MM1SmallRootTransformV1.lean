-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MM1SmallRootTransformV1
-- name    : Kyprianou.Ch04.exercise46MM1SmallRootTransformV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T00:40:14.509127+00:00
-- url     : https://prove2.me/theorems/e6d02d48-5a28-4804-aa9a-0208ee0930af
-- title:
--   Small-root M/M/1 fluctuation transform limit
-- statement:
--   Small-root M/M/1 fluctuation transform limit.
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MM1SmallRootTransformV1
    (lambda mu beta : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hbeta : 0 < beta) :
    let psi : Real → Real := fun x => x - lambda*x/(mu+x)
    Tendsto (fun phi : Real =>
      (psi phi / phi) * ((beta-phi)/(psi beta-psi phi)))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((1-lambda/mu)*(1+lambda/(mu-lambda+beta)))) := by
  sorry
