-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_corollary_A_4
-- name    : LogSobolevMC.TwoPoint.corollary_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:58.064977+00:00
-- url     : https://prove2.me/theorems/da87fe35-6be0-40ff-acd8-bb6a0319775b
-- title:
--   Corollary A.4, p. 747 — α(K) ≥ (1 − 2π_*)λ(K)/log[1/π_* − 1] for every finite chain
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$ with invariant probability $\pi>0$, and $\pi_*=\min_{\mathcal X}\pi$. Its spectral gap $\lambda(K)$ and log-Sobolev constant $\alpha(K)$ satisfy
--
--   $$\alpha(K)\ge\frac{(1-2\pi_*)\,\lambda(K)}{\log[1/\pi_*-1]}.$$
--
--   This turns any spectral gap estimate into a log-Sobolev estimate losing only a factor of order $\log(1/\pi_*)$.
--
--   **Formalization Note** No irreducibility, reversibility or bound on $\pi_*$ is assumed. In the degenerate case $\pi_*=1/2$ (uniform measure on two points) and on a one-point set the right side is a Lean default value $0$ and the inequality reduces to $\alpha\ge0$.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 747, Corollary A.4

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- Corollary A.4 (p. 747): for any finite Markov chain `K` with positive invariant measure `π`,
`α(K) ≥ (1 − 2π_*)λ(K)/log[1/π_* − 1]`. -/
theorem corollary_A_4 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) :
    (1 - 2 * piMin π) * LogSobolevMC.ChiSquare.gap K π / Real.log (1 / piMin π - 1) ≤ LogSobolevMC.ChiSquare.logSobolev K π := by sorry

end LogSobolevMC.TwoPoint
