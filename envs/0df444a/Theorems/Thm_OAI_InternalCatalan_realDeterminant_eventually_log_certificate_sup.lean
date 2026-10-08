-- Prove2me | Theorems.Thm_OAI_InternalCatalan_realDeterminant_eventually_log_certificate_sup
-- name    : OAI.InternalCatalan.realDeterminant_eventually_log_certificate_sup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:52.262556+00:00
-- url     : https://prove2.me/theorems/bba274db-3866-4018-8091-8e74e3a2c8a3
-- title:
--   OpenAI Catalan, Propositions 5.2, 5.3, 6.1 — the real-place bound for log|Δ_N|/n² by the two-case certificate supremum
-- statement:
--   Let $\Delta_N$ be the real determinant of the paper's Eq. (7) (`determinant N`), $n=48N$, and let $B^\ast$ be the larger of the right-hand sides of Eq. (78) in the two cases $\kappa=1,2$, evaluated at the trial sequences and multipliers of §7.1 (`realDeterminantCertificateSupBound`):
--
--   $$B^\ast=\max_{\kappa\in\{1,2\}}\Big[-\tfrac{11}{16}\log2+\kappa\|p_\kappa\|_*^2+\tfrac12\|v_\kappa\|_*^2+\sup_{\substack{-1\le x<1\\x\ne0}}X_\kappa(x)+\sup_{0<s<1}Y_\kappa(s)\Big].$$
--
--   Then for every $d>0$, for all sufficiently large $N$,
--
--   $$\Delta_N\ne0\ \Longrightarrow\ \frac{\log|\Delta_N|}{n^2}-\frac{\log2}{2}\le B^\ast+d .$$
--
--   This is the analytic heart of the real-place estimate: $\Delta_N$ is written as an integral over configurations of points, bounded by an interpolation estimate (Proposition 5.2) on one range of configurations and a Hadamard estimate (Proposition 5.3) on the other, and the resulting energies are bounded through the Chebyshev expansion of the logarithmic kernel by the trial-sequence duality of Proposition 6.1.
--
--   OpenAI, p. 31: “Consequently the maximum of the right sides for the two cases bounds $\limsup_{N\to\infty}\big(n^{-2}\log|\Delta_N|-\frac12\log2\big)$.”
--
--   **Formalization note.** The statement is the eventual form of the $\limsup$ bound, for the specific trial data of §7.1; $-\tfrac{11}{16}=-1+\alpha+\gamma$ (p. 41). $\log$ is `Real.log`, and suprema are `sSup` of the image sets. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 28-34, Propositions 5.2, 5.3 and 6.1 (Eq. (78))

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan

open Set Filter
open scoped BigOperators

theorem realDeterminant_eventually_log_certificate_sup {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        realDeterminantCertificateSupBound + d := by
  sorry

end OAI.InternalCatalan
