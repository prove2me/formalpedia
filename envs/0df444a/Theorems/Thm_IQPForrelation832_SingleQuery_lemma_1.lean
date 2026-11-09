-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_lemma_1
-- name    : IQPForrelation832.SingleQuery.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:08:07.513188+00:00
-- url     : https://prove2.me/theorems/ca75d8b9-fe09-4a33-a03b-d1c4a742fe09
-- title:
--   Lemma 1 — odd quadratic phase Fourier sin
-- statement:
--   For every natural dimension $n$, define $\sigma_{\rm odd}(x)=\sqrt2(-1)^{Q(x)}$ when $|x|$ is odd, and zero otherwise. Its orthonormal Fourier transform satisfies
--   $$
--   \widehat\sigma_{\rm odd}(x)=\sqrt2\sin\!\left(\frac\pi4(n-2|x|)\right)\qquad(x\in V_n).
--   $$
--   In particular, if $n$ is odd then $|\widehat\sigma_{\rm odd}(x)|=1$ for every $x$.
--
--   Both the transform formula and the conditional unit-modulus assertion are retained. These statements supply the exact transform values needed for the respective accepting predicate; the angle uses ordinary real subtraction even at high Hamming weights.
--
--   Differences from the source:
--   - generalization: the formula is stated inside the section on odd n → the transform formula holds for every natural n, with unit modulus still conditional on Odd n; reason: the source calculation holds at every n and the conditional clause recovers the entire odd-dimensional statement
--   - encoding: orthonormal transform and angle n-2|x| → realFourier with reciprocal sqrt(2^n) and subtraction after casting to the reals; reason: the real transform is the real-valued specialization of the complex transform and casting prevents truncated natural subtraction
--   - encoding: binary strings and real sign-valued functions → Cube n = Fin n → ZMod 2 and real functions with an explicit IsSign predicate; reason: the coordinatewise Bool equivalence preserves every string, XOR, pairing and sign value, including dimension zero
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 17, Lemma 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Programs

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

theorem lemma_1 (n : ℕ) :
    (∀ x : Cube n, realFourier sigmaOdd x =
      Real.sqrt 2 * Real.sin (Real.pi / 4 * ((n : ℝ) - 2*(weight x : ℝ)))) ∧
    (Odd n → ∀ x : Cube n, |realFourier sigmaOdd x| = 1) := by sorry

end IQPForrelation832.SingleQuery
