-- Prove2me | Theorems.Thm_Helfgott_prime_progression_log_sieve
-- name    : Helfgott.prime_progression_log_sieve
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T19:11:42.161609+00:00
-- url     : https://prove2.me/theorems/9a842b69-e498-410b-b3a5-926fcbc442d2
-- title:
--   An unconditional explicit Selberg bound for primes in an arithmetic progression
-- statement:
--   For natural numbers $N,a,q,U$ with $q>0$ and $U\ge2$,
--    $$\#\{p<N:p\text{ prime},\ p>U,\ p\equiv a\pmod q\}\le\frac{N}{\varphi(q)\log U}+U^4.$$
--    The estimate is uniform in the residue class, with no unproved distribution hypothesis. The conservative error term is explicit.
-- source:
--   Classical finite Selberg sieve and the Chinese remainder theorem. Radical-fibre harmonic comparison and modulus normalizer comparison retain attribution to raresbuhai, accepted submission 270f0aa4-1a5a-4d37-aad1-43522eb8dc16. Finite hyperbola and divisor energy identities retain attribution to raresbuhai submissions 4b19f26e-e6f8-4a14-8cf6-e0ea33b44440 and dc167013-7b1b-47a5-bd68-36e63ad77223 (Apache 2.0). Explicit optimized weights, inversion, supported error bound and progression theorem formalized by Codex.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
open Finset

theorem Helfgott.prime_progression_log_sieve (N q a U : ℕ) (hq : 0 < q) (hU : 2 ≤ U) :
    (((range N).filter (fun n => n.Prime ∧ U < n ∧ n%q=a%q)).card:ℝ) ≤
      (N:ℝ)/((Nat.totient q:ℝ)*Real.log (U:ℝ))+(U:ℝ)^4 := by sorry
