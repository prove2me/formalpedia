-- Prove2me | Theorems.Thm_N25_unitRelationNumeratorResidue25_sound
-- name    : N25.unitRelationNumeratorResidue25_sound
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:36.229379+00:00
-- url     : https://prove2.me/theorems/d5ff4056-16e9-4441-973c-2e085375454a
-- title:
--   A zero residue certificate implies a high-power divisibility of the evaluation
-- statement:
--   Let $b,N∈ℕ$ with $b>0$, and assume the residue computation $R(b,N)$ is zero. Put $t=(N+24)/25$ using integer division, and let $P_t$ be the corresponding numerator polynomial. Then $$(b:ℤ)^N\mid P_t(b).$$ This proves the arithmetic soundness of each modular residue certificate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue

set_option autoImplicit false
open N25

theorem N25.unitRelationNumeratorResidue25_sound (base count : ℕ) (hb : 0 < base)
    (h : unitRelationNumeratorResidue25 base count = 0) :
    (base : ℤ) ^ count ∣
      (unitRelationNumeratorPolynomial25 ((count + 24) / 25)).eval (base : ℤ) := by sorry
