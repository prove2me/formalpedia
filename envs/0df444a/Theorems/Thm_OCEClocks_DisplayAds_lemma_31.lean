-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_31
-- name    : OCEClocks.DisplayAds.lemma_31
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:23:55.920399+00:00
-- url     : https://prove2.me/theorems/04bd6a16-fa18-4658-9225-faf780b0c3da
-- title:
--   Lemma 31 — the potential $\Gamma$ solves the ODE (32)
-- statement:
--   Let $\lambda>0$ and let $\Gamma$ be the potential (6). Then $\Gamma$ is continuously differentiable on ages $a\ge0$, with
--
--   $$\Gamma'(a)=(1+\lambda+e^{-\lambda})\Gamma(a)-e^{-\lambda}-\lambda\Gamma(0)-\lambda\big(1-\Gamma(0)\big)e^{-\lambda e^{-\lambda a}}.\qquad(32)$$
--
--   Together with Lemma 14, this ODE gives the bound on $\Gamma-L_G\Gamma$ used in Lemma 19 and the identity for $\Gamma^\star$ in Appendix B.2.
--
--   **Formalization Note** For every $a\ge0$, $\Gamma$ has derivative (32) at $a$ within $[0,\infty)$; this is the ordinary derivative for $a>0$ and the right derivative at $a=0$. The right side of (32) is continuous on $[0,\infty)$, which is the "continuously" in the claim.
--
--   Differences from the source:
--   - generalization: λ = 4.5 ("The rest of the paper fixes λ = 4.5", p. 9) → every λ > 0; reason: the printed statement does not depend on the value of λ; at λ = 9/2 the Lean statement is the paper's
--   - reading: M⋆_x = lim_{ε↓0}(M_ε)^{x/ε}, formally exp(x L_M), in the potential Γ (6) and Γ⋆ = πΓ (7) → (M⋆_x 1)(a) is the probability that the infinitesimal-request age process started at age a has not stopped by time x; reason: the operator limit is informal in the paper; the paper identifies M⋆_x 1 with exactly this survival probability (p. 11 and the proof of Lemma 30)
--   - encoding: Γ′(a) for ages a ≥ 0 → derivative within [0, ∞) (ordinary for a > 0, right derivative at a = 0); reason: Γ is a function on ages [0, ∞); same claim
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 38, Lemma 31, eq. (32)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Potential

namespace OCEClocks.DisplayAds

/-- Lemma 31 (p. 38), eq. (32): `Γ` is continuously differentiable on ages `a ≥ 0` (right
derivative at `0`) with
`Γ'(a) = (1 + λ + e^{-λ}) Γ(a) - e^{-λ} - λ Γ(0) - λ (1 - Γ(0)) e^{-λ e^{-λ a}}`. -/
theorem lemma_31 (lam : ℝ) (hlam : 0 < lam) :
    (∀ a : ℝ, 0 ≤ a → HasDerivWithinAt (potential lam)
      ((1 + lam + Real.exp (-lam)) * potential lam a - Real.exp (-lam) - lam * potential lam 0 -
        lam * (1 - potential lam 0) * Real.exp (-(lam * Real.exp (-(lam * a)))))
      (Set.Ici 0) a) ∧
    ContinuousOn (fun a => (1 + lam + Real.exp (-lam)) * potential lam a - Real.exp (-lam) -
        lam * potential lam 0 - lam * (1 - potential lam 0) * Real.exp (-(lam * Real.exp (-(lam * a)))))
      (Set.Ici 0) := by sorry

end OCEClocks.DisplayAds
