-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_4_7
-- name    : KSATSingleFlip.Connect.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:06:59.867007+00:00
-- url     : https://prove2.me/theorems/56364b69-baa7-45fd-9458-773eae4cf179
-- title:
--   Lemma 4.7 — near-critical escape: $r_0 = O(\delta^{-1})$, $\prod\max\{1,m^\gamma_{r+1}\} = O(\delta^{-8})$
-- statement:
--   For sufficiently small $\delta>0$ and every $\gamma\le\gamma^*-\delta$, the first depth $r_0 = \min\{r\ge1 : h^\gamma_r>13\}$ satisfies
--   $$r_0 = O(\delta^{-1}),\qquad \prod_{r=1}^{r_0-1}\max\{1,m^\gamma_{r+1}\} = O(\delta^{-8}).$$
--   In Lean: there are absolute $C>0$ and $\delta_0>0$ such that for $0<\delta<\delta_0$ and $\gamma\le\gamma^*-\delta$, the set $\{r\ge1 : h^\gamma_r>13\}$ is nonempty, its least element $r_0$ satisfies $r_0\le C/\delta$, and the product (in $[0,\infty]$) is at most $C/\delta^8$.
--
--   Differences from the source:
--   - encoding: O(δ⁻¹), O(δ⁻⁸) for sufficiently small δ → ∃ C > 0, ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀): r₀ ≤ C/δ and product ≤ C/δ⁸; reason: the O-constants are absolute (they depend on nothing)
--   - encoding: r₀ = min{r ≥ 1 : h^γ_r > 13} → existence of such r stated as a conjunct; r₀ = sInf of the set; reason: the source's min presupposes the set is nonempty; stating it avoids the ℕ-sInf junk value 0
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 4.7, printed p. 24 (PDF 26)

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField

open scoped Classical BigOperators ENNReal

namespace KSATSingleFlip.Connect

/-- Lemma 4.7 (near-critical escape; printed p. 24). For sufficiently small `δ > 0` and
`γ ≤ γ* − δ`, the first depth `r₀ = min{r ≥ 1 : h^γ_r > 13}` exists, `r₀ ≤ C/δ`, and
`∏_{r=1}^{r₀−1} max{1, m^γ_{r+1}} ≤ C δ^{−8}`, with an absolute constant `C` (the `O(·)`). -/
theorem lemma_4_7 :
    ∃ C : ℝ, 0 < C ∧ ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ γ : ℝ, γ ≤ gammaStar - δ →
        (∃ r : ℕ, 1 ≤ r ∧ 13 < hIter γ r) ∧
        ((sInf {r : ℕ | 1 ≤ r ∧ 13 < hIter γ r} : ℕ) : ℝ) ≤ C / δ ∧
        ∏ r ∈ Finset.Ico 1 (sInf {r : ℕ | 1 ≤ r ∧ 13 < hIter γ r}), max 1 (mIter γ (r + 1)) ≤
          ENNReal.ofReal (C / δ ^ 8) := by sorry

end KSATSingleFlip.Connect
