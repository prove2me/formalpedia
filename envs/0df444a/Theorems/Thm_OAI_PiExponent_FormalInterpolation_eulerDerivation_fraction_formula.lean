-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eulerDerivation_fraction_formula
-- name    : OAI.PiExponent.FormalInterpolation.eulerDerivation_fraction_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:01:09.147066+00:00
-- url     : https://prove2.me/theorems/2cc99063-b261-4863-b7f3-bcc81256c175
-- title:
--   Euler derivation formula on a reduced rational function
-- statement:
--   Every rational function has a coprime polynomial fraction representation for which its image under a derivation sending X to X satisfies the quotient-rule identity d(r)q² = X(p′q − pq′).

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic

open RatFunc

theorem OAI.PiExponent.FormalInterpolation.eulerDerivation_fraction_formula
    (K : Type) [Field K] [CharZero K]
    (d : Derivation K (RatFunc K) (RatFunc K))
    (hdX : d RatFunc.X = RatFunc.X)
    (r : RatFunc K) :
    ∃ p q : Polynomial K,
      r = (p : RatFunc K) / (q : RatFunc K) ∧
      q ≠ 0 ∧ IsCoprime p q ∧
      d r * (q : RatFunc K) ^ 2 =
        RatFunc.X *
          (((p.derivative : Polynomial K) : RatFunc K) * (q : RatFunc K) -
            (p : RatFunc K) * ((q.derivative : Polynomial K) : RatFunc K)) := by sorry
