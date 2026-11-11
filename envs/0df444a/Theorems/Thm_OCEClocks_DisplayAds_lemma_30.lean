-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_30
-- name    : OCEClocks.DisplayAds.lemma_30
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:24:11.234253+00:00
-- url     : https://prove2.me/theorems/d7f0cf13-90f4-470b-81f1-2d5dad266a69
-- title:
--   Lemma 30 — closed form (31) of the potential $\Gamma$ in terms of $\Gamma(0)$; $\Gamma$ is nondecreasing
-- statement:
--   Let $\lambda>0$, and let $\Gamma$ be the potential (6), $\Gamma(a)=1-\int_0^\infty e^{-x}(M^\star_x\mathbf 1)(a)\,dx$. For every age $a\ge0$,
--
--   $$\Gamma(a)=\int_0^\infty e^{-(1+\lambda+e^{-\lambda})t}\Big(e^{-\lambda}+\lambda\Gamma(0)+\lambda\big(1-\Gamma(0)\big)e^{-\lambda e^{-\lambda(a+t)}}\Big)\,dt.\qquad(31)$$
--
--   In particular, $\Gamma$ is nondecreasing on $[0,\infty)$.
--
--   This closed form is the basis of the numerical value of $\Gamma^\star$ (Appendix B.2), the ODE of Lemma 31 and the certified computations of Lemma 18.
--
--   **Formalization Note** The integral is over $t\in(0,\infty)$. Monotonicity is `MonotoneOn` on $[0,\infty)$.
--
--   Differences from the source:
--   - generalization: λ = 4.5 ("The rest of the paper fixes λ = 4.5", p. 9) → every λ > 0; reason: the printed statement does not depend on the value of λ; at λ = 9/2 the Lean statement is the paper's
--   - reading: M⋆_x = lim_{ε↓0}(M_ε)^{x/ε}, formally exp(x L_M), in the potential Γ (6) and Γ⋆ = πΓ (7) → (M⋆_x 1)(a) is the probability that the infinitesimal-request age process started at age a has not stopped by time x; reason: the operator limit is informal in the paper; the paper identifies M⋆_x 1 with exactly this survival probability (p. 11 and the proof of Lemma 30)
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 37, Lemma 30, eq. (31) (proof p. 38)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Potential

open MeasureTheory

namespace OCEClocks.DisplayAds

/-- Lemma 30 (p. 37), eq. (31): the potential in terms of `Γ(0)`; in particular `Γ` is
nondecreasing on ages. -/
theorem lemma_30 (lam : ℝ) (hlam : 0 < lam) :
    (∀ a : ℝ, 0 ≤ a → potential lam a =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-((1 + lam + Real.exp (-lam)) * t)) *
        (Real.exp (-lam) + lam * potential lam 0 +
          lam * (1 - potential lam 0) * Real.exp (-(lam * Real.exp (-(lam * (a + t))))))) ∧
    MonotoneOn (potential lam) (Set.Ici 0) := by sorry

end OCEClocks.DisplayAds
