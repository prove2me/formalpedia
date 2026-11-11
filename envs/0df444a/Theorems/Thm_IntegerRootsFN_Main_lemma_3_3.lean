-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_lemma_3_3
-- name    : IntegerRootsFN.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:43.714803+00:00
-- url     : https://prove2.me/theorems/5c0f788e-0edc-4951-a608-bee3e1369577
-- title:
--   Lemma 3.3 — Gaussian integer shift and all shifted coefficients
-- statement:
--   For every degree $d\ge1$ integer polynomial $g$ and every integer $b\ge1$ with $|g_j|<2^b$, a single deterministic machine computes a Gaussian integer $q$ and all $d+1$ Gaussian integer coefficients $c_j$ of $g(q+x)$, with
--
--   $$|q|\le10d^2+1,\qquad \forall\alpha\text{ a root of }g,\quad |\alpha-q|>1.$$
--
--   The joint time is $\widetilde O(d(b+d))$, and each coefficient's represented bit length is $\widetilde O(b+d)$. Constants and fixed logarithmic exponents are uniform over $d,b,g$; logs involve only $d,b$. The returned finite circle samples also certify the actual rounding and exact-maximization construction of pp.8–9, and their output is charged.
--
--   This supplies a computable shift and shifted coefficients without a root-clearance promise on the input.
--
--   Differences from the source:
--   - encoding: integers n,b≥1 and coefficients given in binary → positive natural parameters, dense signed fixed-width coefficients, finite signed binary outputs; reason: this represents every source input; signs, delimiters, input reads and output writes count as machine steps
--   - encoding: uniform soft-O bit-operation bounds → one finite deterministic multitape machine and positive global C with fixed natural exponents k,l before all varying inputs, bounded by CF(1+log₂(n+1))^k(1+log₂(b+1))^l; reason: shifted logarithms cover the small inputs without changing the allowed polynomial or logarithmic scope; finite initially blank work tapes prohibit advice or assigned costs
--   - encoding: intermediate arithmetic in the specified construction on pp.8–10 → the finite dyadic circle samples, selected Gaussian integer and, for approximation, common-dyadic factors are also emitted; reason: these are computed intermediate records of the source procedure; emitting them charges their representation and pins the construction rather than assuming a successful approximation
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 8, Lemma 3.3

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ApproximationConstruction

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem lemma_3_3 :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
    ∀ (d b : ℕ) (g : Polynomial ℤ), Valid g d b →
    ∃ (samples : Fin (d + 1) → ApproxGKR.GaussDyadic) (q : ℤ × ℤ) (cs : List (ℤ × ℤ)),
      ShiftChoice g d samples q ∧ cs.length = d + 1 ∧
      (∀ j : ℕ, (DyadicPolynomial.value ⟨0, cs⟩).coeff j = (shiftPolynomial g q).coeff j) ∧
      ‖gaussianValue q‖ ≤ 10 * (d : ℝ) ^ 2 + 1 ∧
      (∀ α : ℂ, (complexify g).IsRoot α → 1 < ‖α - gaussianValue q‖) ∧
      (∀ z ∈ cs, (magnitudeLength z.1 + magnitudeLength z.2 : ℕ) ≤
        softBound C k l d b ((b : ℝ) + d)) ∧
      Runs M (polynomialWord g d b)
        (IntMul.joinSep [samplesWord samples, gaussianWord q, gaussiansWord cs])
        (softBound C k l d b ((d : ℝ) * (b + (d : ℝ)))) := by sorry

end IntegerRootsFN.Main
