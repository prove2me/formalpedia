-- Prove2me | Theorems.Thm_GloriaOtto_Variance_proposition_2_1
-- name    : GloriaOtto.Variance.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:15.342076+00:00
-- url     : https://prove2.me/theorems/873bffc1-9112-48d1-bd2e-91e1400e3156
-- title:
--   Proposition 2.1 — ⟨|φ_T(0)|^q⟩ ≤ C_q (ln T)^{γ(q)} for d = 2 and ≤ C_q for d > 2, with γ(2n) = n(n+1) for n = 2^l
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$. There is a function $\gamma : \mathbb R_+ \to \mathbb R_+$, continuous on $[0,\infty)$, such that:
--
--   1. for every $q \ge 0$ there is a constant $C_q$ such that for every probability law $\nu$ on $\mathbb R$ with $\nu([\alpha,\beta]) = 1$, every $\xi \in \mathbb R^d$ with $|\xi| = 1$ and every $T > 0$, under the i.i.d. law $\nu^{\otimes E}$,
--   $$\langle|\phi_T(0)|^q\rangle \le C_q(\ln T)^{\gamma(q)}\quad (d = 2,\ T \ge e), \qquad \langle|\phi_T(0)|^q\rangle \le C_q \quad (d > 2); \tag{2.6}$$
--   2. $\gamma(2n) = n(n+1)$ for all $n = 2^l$ with $l \in \mathbb N$ large enough.
--
--   All finite moments of the approximate corrector are thus bounded independently of $T$ for $d > 2$, and grow at most logarithmically in $T$ for $d = 2$. This is the main ingredient of the proof of Theorem 2.1.
--
--   **Formalization Note.** For $d = 2$ the bound is stated for $T \ge e$. As printed ("for all $T>0$") it fails at $T = 1$, where $\ln T = 0$ while $\langle|\phi_T(0)|^q\rangle > 0$ for non-degenerate laws, and $(\ln T)^{\gamma(q)}$ is undefined for $T < 1$. The proof uses $\mu_2(T) = \ln T$ for $T \gg 1$. $\gamma$ is a real function required to be continuous and nonnegative on $[0,\infty)$. The constants are chosen before $\nu$, $\xi$ and $T$; the expectation is a lower Lebesgue integral in $[0,\infty]$.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Proposition 2.1, (2.6), p. 12

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem proposition_2_1 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ γ : ℝ → ℝ, ContinuousOn γ (Set.Ici 0) ∧ (∀ s, 0 ≤ s → 0 ≤ γ s) ∧
      (∀ q : ℝ, 0 ≤ q → ∃ C : ℝ, ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
        ν (Set.Icc α β)ᶜ = 0 → ∀ ξ : Fin d → ℝ, sqNorm ξ = 1 → ∀ T : ℝ, 0 < T →
          (d = 2 → Real.exp 1 ≤ T →
            ∫⁻ a, ENNReal.ofReal (|phiT a T ξ 0| ^ q) ∂(law d ν)
              ≤ ENNReal.ofReal (C * Real.log T ^ γ q)) ∧
          (2 < d →
            ∫⁻ a, ENNReal.ofReal (|phiT a T ξ 0| ^ q) ∂(law d ν) ≤ ENNReal.ofReal C)) ∧
      ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l →
        γ (2 * (2 : ℝ) ^ l) = (2 : ℝ) ^ l * ((2 : ℝ) ^ l + 1) := by sorry

end GloriaOtto.Variance
