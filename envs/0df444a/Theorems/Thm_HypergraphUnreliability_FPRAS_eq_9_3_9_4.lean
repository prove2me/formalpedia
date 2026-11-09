-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_eq_9_3_9_4
-- name    : HypergraphUnreliability.FPRAS.eq_9_3_9_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:08.2572+00:00
-- url     : https://prove2.me/theorems/233efdd8-c848-40ff-931f-91948ca5c32e
-- title:
--   Equations (9.2)–(9.4) and $0<\Lambda\le R$ — rate rounding and stability
-- statement:
--   On the connected quotient with $0<p_e<1$ written as a fraction, let $r_e=-\log p_e$, $\tau=\varepsilon/(64m)$, and let $l_e$, $a$, $r^\prime_e$, $R$ be the rounding of §9.1. Let $b_e$ be the binary length of the written denominator of $p_e$. Then:
--
--   1. $l_e\le r_e$ and $r_e-l_e\le\tau/4$;
--   2. $2^{-a}\le\tau/4$, and every $r^\prime_e$ is an integer multiple of $2^{-a}$;
--   3. $0<r_e\le r^\prime_e\le r_e+\tau/2$;
--   4. $R\le\sum_e b_e+m\tau$;
--   5. $0<\Lambda\le R$;
--   6. with $p^\prime_e=e^{-r^\prime_e}$ and $u^\prime=u(p^\prime)$,
--   $$e^{-\varepsilon/64}u(p)\le u^\prime\le e^{\varepsilon/64}u(p),\qquad u^\prime\le u(p).$$
--
--   These are the properties of the rounded rates used by the rest of §9: positivity, polynomial numerical size, a common denominator, and the relative comparison with the target.
--
--   Differences from the source: none.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §9.1, (9.2)–(9.4), p. 13; §9.2, p. 13

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_WeightedAlgorithm

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- (9.2)–(9.5), pp. 13: logarithmic rate rounding and the stability it gives. For the connected
quotient and rational `ε ∈ (0,1)`, with `r_e = -log p_e` and `τ = ε/(64 m)`:
`l_e ≤ r_e`, `r_e - l_e ≤ τ/4`; every `r′_e` is a multiple of `2^{-a}`, `2^{-a} ≤ τ/4`;
`0 < r_e ≤ r′_e ≤ r_e + τ/2`; `R = ∑_e r′_e ≤ ∑_e b_e + m τ`; `0 < Λ ≤ R`; and (9.4):
`e^{-ε/64} u(p) ≤ u′ ≤ e^{ε/64} u(p)`, together with `u′ ≤ u(p)`. -/
theorem eq_9_3_9_4 (D : QuotientData) (hD : D.Regular) (ε : ℚ) (h0 : 0 < ε) (h1 : ε < 1) :
    (∀ e, ((D.lowerRate ε e : ℚ) : ℝ) ≤ -Real.log (D.failProb e) ∧
      -Real.log (D.failProb e) - ((D.lowerRate ε e : ℚ) : ℝ) ≤ ((D.τ ε / 4 : ℚ) : ℝ)) ∧
    (1 / 2 : ℚ) ^ D.a ε ≤ D.τ ε / 4 ∧
    (∀ e, ∃ c : ℤ, D.roundedRate ε e = (c : ℚ) * (1 / 2 : ℚ) ^ D.a ε) ∧
    (∀ e, 0 < -Real.log (D.failProb e) ∧
      -Real.log (D.failProb e) ≤ D.roundedRateReal ε e ∧
      D.roundedRateReal ε e ≤ -Real.log (D.failProb e) + ((D.τ ε / 2 : ℚ) : ℝ)) ∧
    D.R ε ≤ ((∑ e, Nat.size (D.fail e).den : ℕ) : ℚ) + (D.m : ℚ) * D.τ ε ∧
    0 < D.Lam ε ∧ D.Lam ε ≤ D.R ε ∧
    Real.exp (-((ε : ℝ) / 64)) * D.target ≤ D.comparisonTarget ε ∧
    D.comparisonTarget ε ≤ Real.exp ((ε : ℝ) / 64) * D.target ∧
    D.comparisonTarget ε ≤ D.target := by sorry

end HypergraphUnreliability.FPRAS
