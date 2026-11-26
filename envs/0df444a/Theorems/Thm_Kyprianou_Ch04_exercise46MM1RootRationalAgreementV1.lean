-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MM1RootRationalAgreementV1
-- name    : Kyprianou.Ch04.exercise46MM1RootRationalAgreementV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T00:43:46.815801+00:00
-- url     : https://prove2.me/theorems/93745a9a-94ba-5cc4-861b-bc25f3f3aa3f
-- title:
--   M/M/1 exponential-time rational cancellation
-- statement:
--   M/M/1 exponential-time rational cancellation
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MM1RootRationalAgreementV1
    (lambda mu beta phi : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hbeta : 0 < beta)
    (hphi : 0 < phi) (hpb : phi < beta) :
    let psi : Real → Real := fun x => x - lambda*x/(mu+x)
    (psi phi / phi) * ((beta-phi)/(psi beta-psi phi)) =
      (phi+mu-lambda)*(mu+beta) /
        ((mu+beta)*(mu+phi)-lambda*mu) := by
  sorry
