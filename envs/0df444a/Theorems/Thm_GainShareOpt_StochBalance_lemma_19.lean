-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_19
-- name    : GainShareOpt.StochBalance.lemma_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:48:48.185195+00:00
-- url     : https://prove2.me/theorems/a450682e-da4b-4181-985b-597055246f6c
-- title:
--   Lemma 19 — exact-profile and return-value enclosures (98)–(101)
-- statement:
--   Let $\alpha\in\{a,b\}$ and let $u$ satisfy (93)–(97). Then $y_\alpha$ reaches $1/e$ at a time $\tau_\alpha\in(0,\eta)$ while remaining strictly below $e^{-t}$; its constant extension $g_\alpha$ lies in $G$ and satisfies all partial-load constraints $H_{g_\alpha}(t,s)\ge\alpha$; and
--   $$\|y_\alpha-u\|_{\infty,[0,\eta]}<\frac1{5000},\qquad |q(\alpha)-\hat Q_\alpha|<\frac1{10000}, \tag{98–99}$$
--   where $\hat Q_\alpha:=A(u)=1-e^{-(\eta+1)}-\int_0^\eta e^{-z}u(z)\,dz$ (100) and $q(\alpha):=A(g_\alpha)=\int_0^{\tau_\alpha}e^{-z}(1-y_\alpha(z))\,dz+(1-1/e)e^{-\tau_\alpha}$ (101). No feasibility assumption on $\alpha$ is needed.
--
--   Combined with the verifier's enclosures of $\hat Q_a,\hat Q_b$, it yields Corollary 2.
--
--   Differences from the source:
--   - encoding: nodal values (u_i)_{0≤i≤K} → uN : ℕ → ℝ, of which only uN 0, …, uN K enter; reason: every nodal vector extends to such a sequence
--   - encoding: α ∈ {a, b} with a = 0.5802, b = 0.5805 → α = 2901/5000 ∨ α = 1161/2000; reason: decimals as exact rationals
--   - encoding: the decreasing branch of y reaches 1/e at a time τ before reaching e^{−t} → τ = hitTime (first t ∈ [0, 1) with y(t) = 1/e) lies in the stated interval, y(τ) = 1/e, y > 1/e on [0, τ), y(t) < e^{−t} on [0, τ]; reason: the first hitting time of 1/e is the τ of the source
--   - encoding: ‖y_α − u‖_{∞,[0,η]} < 1/5000 → ∃ c < 1/5000 with |y_α(t) − u(t)| ≤ c on [0, η]; reason: equivalent to a strict bound on the supremum, and immune to an unbounded-set junk value
--   - encoding: the definitions (100), (101) → stated as equalities: A(u) equals the η-integral form, and q(α) = A(g_α) equals the stopping-time form; reason: the source asserts both identities (end of the proof)
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 63, Lemma 19, (98)–(101)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_Normalized
import Definitions.Def_GainShareOpt_StochBalance_Volterra
import Definitions.Def_GainShareOpt_StochBalance_NodalCert

namespace GainShareOpt.StochBalance

/-- Lemma 19 (exact-profile and return-value enclosures). -/
theorem lemma_19 (α : ℝ) (hα : α = endA ∨ α = endB) (uN : ℕ → ℝ) (hu : NodalHyp α uN) :
    hitTime α ∈ Set.Ioo 0 etaM ∧ fixedProfile α (hitTime α) = Real.exp (-1) ∧
    (∀ t ∈ Set.Ico 0 (hitTime α), Real.exp (-1) < fixedProfile α t) ∧
    (∀ t ∈ Set.Icc 0 (hitTime α), fixedProfile α t < Real.exp (-t)) ∧
    canonProfile α ∈ ClassG ∧
    (∀ t s : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → α ≤ testH (canonProfile α) t s) ∧
    (∃ c : ℝ, c < 1 / 5000 ∧
      ∀ t ∈ Set.Icc 0 etaM, |fixedProfile α t - nodalInterp uN t| ≤ c) ∧
    |returnValue α - scoreA (nodalInterp uN)| < 1 / 10000 ∧
    scoreA (nodalInterp uN) = 1 - Real.exp (-(etaM + 1))
      - ∫ z in (0 : ℝ)..etaM, Real.exp (-z) * nodalInterp uN z ∧
    returnValue α = (∫ z in (0 : ℝ)..(hitTime α), Real.exp (-z) * (1 - fixedProfile α z))
      + (1 - Real.exp (-1)) * Real.exp (-(hitTime α)) := by sorry

end GainShareOpt.StochBalance
