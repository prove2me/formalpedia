-- Prove2me | Theorems.Thm_LLROPI_Shamir_corollary_2_5
-- name    : LLROPI.Shamir.corollary_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:33:50.791499+00:00
-- url     : https://prove2.me/theorems/6493642b-ace0-4bed-84d5-16837db3a984
-- title:
--   Corollary 2.5 — $|\hat g(\xi)|\le\gamma(\rho)+O(p^{-2})$ for $\xi\ne0$; $\gamma$ increases on $(0,1/2]$, decreases on $[1/2,1)$, $\gamma(1/2)=2/\pi$
-- statement:
--   For any $\rho\in(0,1)$ and any $S\subseteq\mathbb F_p$ with $|S|=\rho p$,
--   $$|\hat g(\xi)|\le\gamma(\rho)+O(p^{-2})\qquad\text{for every }\xi\ne0,$$
--   where $g(x)=(1_S(x)-\rho)/\sqrt{\rho(1-\rho)}$ and $\gamma(\rho)=\sin(\pi\rho)/(\pi\sqrt{\rho(1-\rho)})$. Moreover, setting $\gamma(0)=\gamma(1)=0$ by continuity, $\gamma:[0,1]\to[0,\infty)$ is increasing on $(0,1/2]$, decreasing on $[1/2,1)$, and $\gamma(1/2)=2/\pi$.
--
--   Formally: one constant $C$ (before $p$, $S$, $\xi$) with $|\hat g(\xi)|\le\gamma(\rho)+C/p^2$; $\gamma\ge0$ on $[0,1]$; $\gamma(0)=\gamma(1)=0$; $\gamma$ is continuous on $[0,1]$, strictly increasing on $(0,1/2]$, strictly decreasing on $[1/2,1)$; $\gamma(1/2)=2/\pi$.
--
--   Differences from the source:
--   - reading: O(p^{−2}) → one constant C chosen before p, S and ξ, for every prime p; reason: uniform reading, as in Lemma 2.4 (γ ≤ 2/π is bounded)
--   - reading: increasing on (0, 1/2], decreasing on [1/2, 1) → StrictMonoOn on Ioc 0 (1/2), StrictAntiOn on Ico (1/2) 1; reason: the stronger (strict) reading of increasing/decreasing
--   - encoding: setting γ(0) = γ(1) = 0 by continuity, γ : [0, 1] → [0, ∞) → gammaFn 0 = 0, gammaFn 1 = 0, ContinuousOn gammaFn [0, 1] and 0 ≤ gammaFn on [0, 1]; reason: the formula already evaluates to 0 at the endpoints in Lean; the clauses state that this is the continuous extension and that the values are nonnegative
-- source:
--   Sun, Wootters, Improved Local Leakage Resilience of Shamir Secret Sharing and Worst-Case Optimal Polynomial Intersection, arXiv:2610.12357 (held version, sha256 f154f5ce…), Corollary 2.5, (2.1)–(2.2), p. 21 (PDF 23)

import Mathlib
import Definitions.Def_LLROPI_Shamir_Fourier

namespace LLROPI.Shamir

/-- **Corollary 2.5 (L∞-Fourier bound)**, p. 21 (PDF 23). For any `ρ ∈ (0, 1)`,
`|ĝ(ξ)| ≤ γ(ρ) + O(p⁻²)` for every `ξ ≠ 0`, where `g(x) := (1_S(x) − ρ)/√(ρ(1 − ρ))` and
`γ(ρ) := sin(πρ)/(π√(ρ(1 − ρ)))`. Moreover, setting `γ(0) = γ(1) = 0` by continuity,
`γ : [0, 1] → [0, ∞)` is increasing on `(0, 1/2]`, decreasing on `[1/2, 1)`, and `γ(1/2) = 2/π`.
Sun, Wootters, arXiv:2610.12357 (held version, sha256 f154f5ce…), Corollary 2.5, p. 21 (PDF 23).

**Formalization Note.** `S ⊆ 𝔽_p` has density `ρ = |S|/p ∈ (0, 1)`. The `O(p⁻²)` is one constant
`C` chosen before `p`, `S`, `ξ`. "Increasing"/"decreasing" are read strictly. The extension by
continuity is the clause `ContinuousOn γ [0, 1]` (the formula is `0` at `0` and `1`), and
`γ : [0, 1] → [0, ∞)` is the nonnegativity clause. -/
theorem corollary_2_5 :
    (∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)), 0 < density S → density S < 1 →
      ∀ ξ : ZMod p, ξ ≠ 0 →
        ‖fourier (centered S) ξ‖ ≤ gammaFn (density S) + C / (p : ℝ) ^ 2) ∧
    (∀ ρ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ gammaFn ρ) ∧
    gammaFn 0 = 0 ∧ gammaFn 1 = 0 ∧
    ContinuousOn gammaFn (Set.Icc 0 1) ∧
    StrictMonoOn gammaFn (Set.Ioc 0 (1 / 2)) ∧
    StrictAntiOn gammaFn (Set.Ico (1 / 2) 1) ∧
    gammaFn (1 / 2) = 2 / Real.pi := by sorry

end LLROPI.Shamir
