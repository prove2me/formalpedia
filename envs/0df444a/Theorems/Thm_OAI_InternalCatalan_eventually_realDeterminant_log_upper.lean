-- Prove2me | Theorems.Thm_OAI_InternalCatalan_eventually_realDeterminant_log_upper
-- name    : OAI.InternalCatalan.eventually_realDeterminant_log_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:01:10.327874+00:00
-- url     : https://prove2.me/theorems/55699b66-2d67-494f-a130-a21ab44525b7
-- title:
--   OpenAI Catalan, Proposition 7.1 — eventually log|Δ_N|/n² − ½ log 2 < −2.2909
-- statement:
--   Let $\Delta_N$ be the real determinant of the paper's Eq. (7) (`determinant N`) and $n=48N$. Then for all sufficiently large $N$,
--
--   $$\Delta_N\ne0\ \Longrightarrow\ \frac{\log|\Delta_N|}{n^2}-\frac{\log2}{2}<-2.2909 .$$
--
--   This is the real-place upper bound. Combined with the finite-place lower bound $-2.29084$ (Proposition 3.4) along the primes where $\Delta_p\ne0$ (Proposition 4.1), it contradicts the rationality of Catalan's constant.
--
--   OpenAI, p. 34: “Proposition 7.1. For the determinants of Equation (7),
--   $$\limsup_{N\to\infty}\Big(\frac{\log|\Delta_N|}{n^2}-\frac12\log2\Big)\le-2.290939875<-2.2909.\ (88)”$$
--
--   **Formalization note.** The Lean statement is the eventual strict form with the final constant $-2.2909$, a consequence of (88); the sharper constant $-2.290939875$ is not stated. $\log$ is `Real.log`. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 34, 41, Proposition 7.1 (Eq. (88))

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan

open Set Filter

theorem eventually_realDeterminant_log_upper :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 <
        -(22909 / 10000 : ℝ) := by
  sorry

end OAI.InternalCatalan
