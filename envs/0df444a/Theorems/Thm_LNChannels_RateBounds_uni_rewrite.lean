-- Prove2me | Theorems.Thm_LNChannels_RateBounds_uni_rewrite
-- name    : LNChannels.RateBounds.uni_rewrite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:08.197679+00:00
-- url     : https://prove2.me/theorems/707e4a99-fcb7-4b48-9b03-d15c590f1f5f
-- title:
--   Proof of Theorem 2(i), p. 11 — with $\kappa=\log(1+r/\lambda)$ the excess cost of a unidirectional channel is $F(m)$
-- statement:
--   Let $\lambda,r>0$, $B,C\in\mathbb R$, and set $\kappa=\log(1+r/\lambda)$, so that
--   $$\frac{\lambda}{r}=\big(e^{\kappa}-1\big)^{-1}.$$
--   Then for every real size $m>0$ the cost of a unidirectional channel of size $m$ minus the on-chain cost $\lambda C/r$ is
--   $$m+B\Big(\big(1+\tfrac r\lambda\big)^m-1\Big)^{-1}-\frac{\lambda C}{r} = F(m) := \frac{C}{1-e^{\kappa}}+\frac{B}{e^{\kappa m}-1}+m .$$
--
--   This change of variable turns the comparison of Theorem 2(i) into the sign of the one-variable function $F$, which the next milestones minimize.
--
--   **Formalization Note** The channel cost is the closed form `uniCost` of (1) with a real size $m$ and a real power.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 11 (PDF p. 12), proof of Theorem 2(i), display defining F(m)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- Proof of Theorem 2(i), p. 11: with `κ = log(1 + r/λ)`, i.e. `λ/r = (e^κ − 1)⁻¹`, the excess of
the unidirectional channel cost over the on-chain cost `λC/r` is
`F(m) = C/(1 − e^κ) + B/(e^{κm} − 1) + m`. -/
theorem uni_rewrite (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    let κ := Real.log (1 + r / lam)
    lam / r = (Real.exp κ - 1)⁻¹ ∧
      ∀ m : ℝ, 0 < m →
        LNChannels.Exact.uniCost lam r B m - lam * C / r =
          C / (1 - Real.exp κ) + B / (Real.exp (κ * m) - 1) + m := by sorry

end LNChannels.RateBounds
