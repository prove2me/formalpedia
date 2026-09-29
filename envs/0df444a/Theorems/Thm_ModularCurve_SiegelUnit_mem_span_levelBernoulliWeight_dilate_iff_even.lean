-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even
-- name    : ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/db01775e-d2be-5d5a-a5fe-b8c020edda7b
-- title:
--   Dilates of the level-N Bernoulli weight span the even functions
-- statement:
--   Let $N$ be a non-zero natural number and let $\varphi : \mathbb{Z}/N \to \mathbb{Q}$ be an arbitrary rational-valued function on $\mathbb{Z}/N$. For $s \in \mathbb{Z}/N$ consider the function $f_s : \mathbb{Z}/N \to \mathbb{Q}$ given by
--   $$f_s(r) = 6\,\mathrm{val}(sr)^2 - 6N\,\mathrm{val}(sr) + N^2,$$
--   where $sr$ is the product in $\mathbb{Z}/N$, $\mathrm{val}(a) \in \{0,1,\dots,N-1\}$ denotes the least non-negative integer representative of $a \in \mathbb{Z}/N$, and the resulting integer is regarded as a rational number. The index $s$ ranges over all of $\mathbb{Z}/N$, including $s = 0$, for which $f_0$ is the constant function $N^2$. The theorem asserts that $\varphi$ belongs to the $\mathbb{Q}$-linear span of the set $\{f_s : s \in \mathbb{Z}/N\}$ inside the $\mathbb{Q}$-vector space of functions $\mathbb{Z}/N \to \mathbb{Q}$ if and only if $\varphi$ is even, that is, $\varphi(-r) = \varphi(r)$ for every $r \in \mathbb{Z}/N$. Thus the span of the $N$ dilates of the quadratic weight $t \mapsto 6t^2 - 6Nt + N^2$ is exactly the subspace of even functions on $\mathbb{Z}/N$.
--
--   The quadratic weight $6t^2 - 6Nt + N^2 = 6N^2\overline{B}_2(t/N)$ is the normalised periodic second Bernoulli function, and its dilates are the level-$N$ Bernoulli (Stickelberger) distribution of Kubert–Lang; the statement is the one-variable rank computation identifying their span with the even functions. It is used in the construction of prescribed exponent systems for Siegel units, being cited by [`ModularCurve.SiegelUnit.exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub`](thm.html#ModularCurve.SiegelUnit.exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub) and [`ModularCurve.SiegelUnit.exists_peaked_exponent`](thm.html#ModularCurve.SiegelUnit.exists_peaked_exponent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even (N : ℕ) [NeZero N]
    (φ : ZMod N → ℚ) :
    φ ∈ Submodule.span ℚ (Set.range fun s : ZMod N => fun r : ZMod N =>
        ((6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2 : ℤ) : ℚ)) ↔
      ∀ r : ZMod N, φ (-r) = φ r := by sorry
