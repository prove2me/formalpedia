-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_18
-- name    : GainShareOpt.StochBalance.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:48:32.657126+00:00
-- url     : https://prove2.me/theorems/c0ee463d-ce4e-4c68-9fa0-6f5f3209cac0
-- title:
--   Lemma 18 — residual bound $\|T_\alpha u-u\|\le143/6120000$ from the finite tests
-- statement:
--   Let $\alpha\in\{a,b\}$ and let $u$ be the interpolant of nodal values satisfying (93)–(97). Then
--   $$\|T_\alpha u-u\|_{\infty,[0,\eta]}\le\varepsilon,\qquad \varepsilon:=\frac{10^{-6}+2h/3}{1-\eta}=\frac{143}{6120000}.$$
--
--   With the Gronwall estimate this bounds the distance from the exact fixed point (Lemma 19).
--
--   Differences from the source:
--   - encoding: nodal values (u_i)_{0≤i≤K} → uN : ℕ → ℝ, of which only uN 0, …, uN K enter; reason: every nodal vector extends to such a sequence
--   - encoding: α ∈ {a, b} with a = 0.5802, b = 0.5805 → α = 2901/5000 ∨ α = 1161/2000; reason: decimals as exact rationals
--   - encoding: ‖T_α u − u‖_{∞,[0,η]} ≤ ε → |T_α u(t) − u(t)| ≤ ε for all t ∈ [0, η]; reason: a sup-norm bound is a pointwise bound
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 62, Lemma 18

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_Normalized
import Definitions.Def_GainShareOpt_StochBalance_Volterra
import Definitions.Def_GainShareOpt_StochBalance_NodalCert

namespace GainShareOpt.StochBalance

/-- Lemma 18 (residual bound from finite tests). -/
theorem lemma_18 (α : ℝ) (hα : α = endA ∨ α = endB) (uN : ℕ → ℝ) (hu : NodalHyp α uN) :
    (∀ t ∈ Set.Icc 0 etaM,
      |volterraOp α (nodalInterp uN) t - nodalInterp uN t|
        ≤ (1 / 10 ^ 6 + 2 * meshH / 3) / (1 - etaM)) ∧
    (1 / 10 ^ 6 + 2 * meshH / 3) / (1 - etaM) = 143 / 6120000 := by sorry

end GainShareOpt.StochBalance
