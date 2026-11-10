-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_theorem_4_4
-- name    : KSATSingleFlip.Connect.theorem_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:08:09.472266+00:00
-- url     : https://prove2.me/theorems/744a94fb-eaea-4fc0-9621-1522f31dbf56
-- title:
--   Theorem 4.4 — critical threshold of the soft-field recursion: $c_0\le\gamma^*<1$
-- statement:
--   With $\nu^\gamma_0 = 0$, $\nu^\gamma_{r+1} = R_{e^{-\gamma}}\nu^\gamma_r$, $m^\gamma_r = m(\nu^\gamma_r)$, $h^\gamma_r = h(\nu^\gamma_r)$ and $\gamma^* = \inf\{\gamma\in\mathbb R:\sup_{r\ge0}m^\gamma_r<\infty\}$ (4.8): $c_0\le\gamma^*<1$, where $c_0 = 2(\sqrt2-1)$. Specifically:
--   * for $\gamma\ge\gamma^*$, $m^\gamma_r\le1$ for every $r\ge0$, with $m^{\gamma^*}_r\uparrow1$ and $h^{\gamma^*}_r\uparrow\gamma^*$ as $r\to\infty$;
--   * for $\gamma<\gamma^*$, both $m^\gamma_r\uparrow\infty$ and $h^\gamma_r\uparrow\infty$.
--
--   "$\uparrow$" is read as nondecreasing in $r$ and converging (to $+\infty$ for the last two).
--
--   Differences from the source:
--   - encoding: m(ν) = ν(ℝ) ∈ [0,∞) and m_r ↑ ∞ → mIter in ℝ≥0∞; ↑ = Monotone and Tendsto (to 𝓝 ⊤ for the masses, atTop for h); reason: masses are kept in [0,∞] so that "sup < ∞" in (4.8) is literal; every iterate is a finite measure, so no instance changes
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Theorem 4.4 and (4.8), printed p. 21–22 (PDF 23–24)

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField

open scoped Classical BigOperators ENNReal
open Filter Topology

namespace KSATSingleFlip.Connect

/-- Theorem 4.4 (critical threshold of the soft-field recursion; printed pp. 21–22):
`c₀ ≤ γ* < 1`; for `γ ≥ γ*`, `m^γ_r ≤ 1` for every `r`, with `m^{γ*}_r ↑ 1` and `h^{γ*}_r ↑ γ*`;
for `γ < γ*`, `m^γ_r ↑ ∞` and `h^γ_r ↑ ∞`. -/
theorem theorem_4_4 :
    c0 ≤ gammaStar ∧ gammaStar < 1 ∧
    (∀ γ : ℝ, gammaStar ≤ γ → ∀ r : ℕ, mIter γ r ≤ 1) ∧
    (Monotone (mIter gammaStar) ∧ Tendsto (mIter gammaStar) atTop (𝓝 1)) ∧
    (Monotone (hIter gammaStar) ∧ Tendsto (hIter gammaStar) atTop (𝓝 gammaStar)) ∧
    (∀ γ : ℝ, γ < gammaStar →
      (Monotone (mIter γ) ∧ Tendsto (mIter γ) atTop (𝓝 ∞)) ∧
      (Monotone (hIter γ) ∧ Tendsto (hIter γ) atTop atTop)) := by sorry

end KSATSingleFlip.Connect
