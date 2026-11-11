-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_theorem_3_1
-- name    : IntegerRootsFN.Main.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:50.065935+00:00
-- url     : https://prove2.me/theorems/1f07b250-03f7-4aa4-9dad-0350c21c3454
-- title:
--   Theorem 3.1 — Pan approximate factorization
-- statement:
--   Fix any natural input-height multiplier $K$. There are one deterministic finite machine, $C_K>0$ and fixed natural logarithmic exponents, all chosen before the input. Let $p\in\mathbb C[x]$ have degree $d\ge1$, every root in the closed unit disk, and dense coefficients represented as Gaussian integer numerator pairs over a common denominator $2^s$. Let the positive integer precision $P$ satisfy $P\ge d\log_2(d+1)$, $s\le KP$, and let the magnitude length of each numerator component be at most $KP$. The machine computes integer numerator pairs for $d$ dyadics $w_i$ over one denominator $2^B$, with
--
--   $$B\le C_KP,\qquad \left\|p-p_d\prod_{i=1}^d(x-w_i)\right\|_1\le2^{-P}\|p\|_1,$$
--
--   in $\widetilde O(dP)$ actual bit steps, using logarithms only in $d,P$. Here $p_d$ is the original leading coefficient, and $\|\cdot\|_1$ is the sum of absolute coefficient values. The multiplier is fixed before the machine and constants, so they may depend on $K$, never on $d,P,p$.
--
--   This is the supporting theorem as attributed to MSW15 by the source. Remark 3.2, p.8, questions Pan's runtime analysis; the entire computation and runtime remain an open theorem obligation, not an axiom or a hypothesis of the input polynomial.
--
--   Differences from the source:
--   - encoding: coefficient heights and common exponent are O(P) → for every fixed K the common exponent and each real or imaginary numerator length are at most KP, with constants depending only on K; reason: this quantifies the source-allowed height dependence explicitly; bounding the two component lengths individually or their sum differs only by a fixed factor
--   - encoding: uniform soft-O bit-operation bounds → one finite deterministic multitape machine and positive global C with fixed natural exponents k,l before all varying inputs, bounded by CF(1+log₂(n+1))^k(1+log₂(b+1))^l; reason: shifted logarithms cover the small inputs without changing the allowed polynomial or logarithmic scope; finite initially blank work tapes prohibit advice or assigned costs
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 7, Theorem 3.1; Remark 3.2 p.8

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary

set_option autoImplicit false

namespace IntegerRootsFN.Main

/-- Pan's runtime remains an open obligation; see source Remark 3.2. -/
theorem theorem_3_1 :
    ∀ K : ℕ, ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
    ∀ (d P : ℕ) (a : DyadicPolynomial),
      1 ≤ d → 1 ≤ P → a.numerators.length = d + 1 →
      a.value.natDegree = d →
      (∀ α : ℂ, a.value.IsRoot α → ‖α‖ ≤ 1) →
      (d : ℝ) * logTwo ((d : ℝ) + 1) ≤ P →
      a.exponent ≤ K * P →
      (∀ z ∈ a.numerators, magnitudeLength z.1 ≤ K * P ∧ magnitudeLength z.2 ≤ K * P) →
    ∃ (B : ℕ) (ws : Fin d → ℤ × ℤ),
      (B : ℝ) ≤ C * P ∧
      normOne (a.value - factorPolynomial (a.value.coeff d)
        (fun i => ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B))) ≤
          (2 : ℝ) ^ (-(P : ℤ)) * normOne a.value ∧
      Runs M (panInputWord P a) (panOutputWord B (List.ofFn ws))
        (softBound C k l d P ((d : ℝ) * P)) := by sorry

end IntegerRootsFN.Main
