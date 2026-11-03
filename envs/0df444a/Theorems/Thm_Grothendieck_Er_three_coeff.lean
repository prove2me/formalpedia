-- Prove2me | Theorems.Thm_Grothendieck_Er_three_coeff
-- name    : Grothendieck.Er_three_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:39:43.550476+00:00
-- url     : https://prove2.me/theorems/8ee56abc-cf99-4282-81b3-86e883b4cedc
-- title:
--   The rank-three coefficients of $E_3$: $c_0=\frac{8}{3\pi}$, $c_1=\frac{4}{15\pi}$
-- statement:
--   The paper's rank-three rounding function is
--
--   $$
--   E_3(t)=C_3\,t\;{}_2F_1\!\Big(\begin{smallmatrix}1/2,\,1/2\\ 5/2\end{smallmatrix};t^2\Big)
--   =\sum_{k\ge0}c_k\,t^{2k+1},\qquad
--   C_3=\frac23\Big(\frac{\Gamma(2)}{\Gamma(3/2)}\Big)^2=\frac{8}{3\pi},
--   $$
--
--   because $\Gamma(2)=1$ and $\Gamma(3/2)=\sqrt\pi/2$. This node records everything about the coefficient sequence that rank-three rounding arguments use:
--
--   1. $c_k\ge0$ for every $k$;
--   2. $\sum_k c_k$ converges;
--   3. $c_0=\dfrac{8}{3\pi}=0.8488\ldots$;
--   4. $c_1=\dfrac{4}{15\pi}=0.08488\ldots$.
--
--   The two values are forced by the shape of the series — $c_0=C_3$ and $c_1=C_3\cdot\frac{(1/2)^2}{5/2}$ — so they carry no arithmetic beyond $\Gamma(2)=1$ and $\Gamma(3/2)=\sqrt\pi/2$. They are exactly the constants $0.8488$ and $0.08488$ that appear in the rank-three Quantum Max Cut rounding estimates, where the rounding function is this $E_3$ and the pointwise certificate is a comparison of $E_3$ with a line of slope $0.954$.
--
--   **Formalization Note** `ErCoeff`, `Cr` are the mission's definitions; `E_3` itself is `Grothendieck.Er 3`, and `Grothendieck.Er_one` gives $\sum_k c_k=1$.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Lemma 2.1, p. 84 (the series (2.1)) at $r=3$.

import Mathlib
import Definitions.Def_Grothendieck_Series

open scoped BigOperators Real

namespace Grothendieck

/-- **The rank-three coefficients of `E_3`.** All coefficients are nonnegative, the sequence is
summable, and the first two are `8/(3π)` and `4/(15π)`. -/
theorem Er_three_coeff :
    (∀ k : ℕ, 0 ≤ ErCoeff 3 k) ∧ Summable (fun k : ℕ => ErCoeff 3 k) ∧
      ErCoeff 3 0 = 8 / (3 * Real.pi) ∧ ErCoeff 3 1 = 4 / (15 * Real.pi) := by sorry

end Grothendieck
