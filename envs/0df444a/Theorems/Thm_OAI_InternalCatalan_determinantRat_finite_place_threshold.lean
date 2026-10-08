-- Prove2me | Theorems.Thm_OAI_InternalCatalan_determinantRat_finite_place_threshold
-- name    : OAI.InternalCatalan.determinantRat_finite_place_threshold
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:28.443781+00:00
-- url     : https://prove2.me/theorems/2b731862-0ab6-434f-a48c-0baf3e73caa4
-- title:
--   OpenAI Catalan, Proposition 3.4 — finite-place lower bound for log|Δ_N(z)|/n² − ½ log 2
-- statement:
--   For a rational number $z$ and $N\ge1$ let $\Delta_N(z)\in\mathbb Q$ be the determinant of the paper's Eq. (7) with Catalan's constant $G$ replaced by $z$ in the moment evaluations (17) (`determinantRat z N`), and let $n=48N$. Then for all sufficiently large $N$,
--
--   $$\Delta_N(z)\ne0\ \Longrightarrow\ \frac{\log|\Delta_N(z)|}{n^2}-\frac12\log2>-2.29084.$$
--
--   The bound comes from the prime-by-prime denominators of $\Delta_N(z)$ (the odd primes through the digit reductions of §3 and the prime number theorem, the prime $2$ through Proposition 2.2) and the product formula $\log|\Delta|=\sum_p v_p(\Delta)\log p$ for a nonzero rational number.
--
--   OpenAI, p. 17: “Proposition 3.4 (Finite-place bound). Assume $G\in\mathbb Q$. Along any sequence of positive integers $N\to\infty$ for which $\Delta_N\ne0$, one has
--   $$\liminf_{N\to\infty}\Big(\frac{\log|\Delta_N|}{n^2}-\frac12\log2\Big)\ge-\frac{8609}{4608}-\Big(\frac12+\frac{505}{4608}\Big)\log2>-2.29084.\ (42)”$$
--
--   **Formalization note.** The statement is uniform in the rational value $z$ assigned to $G$, and it states the eventual strict inequality with the final constant $-2.29084$, which follows from (42) because the middle constant there exceeds $-2.29084$; the exact middle constant is not stated. $\log$ is `Real.log`. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 17-19, Proposition 3.4

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan

open Filter
open scoped Topology

theorem determinantRat_finite_place_threshold (z : ℚ) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(229084 / 100000 : ℝ) <
        Real.log |(determinantRat z N : ℝ)| / (n N : ℝ) ^ 2 -
          (1 / 2 : ℝ) * Real.log 2 := by
  sorry

end OAI.InternalCatalan
