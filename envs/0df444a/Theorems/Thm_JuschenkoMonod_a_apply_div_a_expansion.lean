-- Prove2me | Theorems.Thm_JuschenkoMonod_a_apply_div_a_expansion
-- name    : JuschenkoMonod.a_apply_div_a_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:22:40.714989+00:00
-- url     : https://prove2.me/theorems/ba77e878-abd2-4744-a916-b0f57794a5fb
-- title:
--   Lemma 2.6 — the expansion (2.v)–(2.vii) of a_{n,g(j)}/a_{n,j}, with constants depending only on |g|_w
-- statement:
--   Write $a_{n,j} = \exp(-ne^{-|j|/n})$. For every real $c$ there are constants $C, C', C''$ with the following property. For every $g \in W(\mathbf Z)$ with $|g|_{\rm w} = c$, every integer $n \ge 1$ and every $j \in \mathbf Z$, there are reals $\eta$ and $\vartheta$ with
--   - (2.v) $\dfrac{a_{n,g(j)}}{a_{n,j}} = \exp\big(e^{-|j|/n}(|g(j)| - |j| + \eta)\big)$ and $|\eta| \le C/n$;
--   - (2.vi) $\dfrac{a_{n,g(j)}}{a_{n,j}} - 1 = e^{-|j|/n}(|g(j)| - |j|) + \eta e^{-|j|/n} + \vartheta$ and $|\vartheta| \le C'e^{-2|j|/n}$;
--   - (2.vii) $\Big|\dfrac{a_{n,g(j)}}{a_{n,j}} - 1\Big| \le C''e^{-|j|/n}$.
--
--   *Formalization note.*
--   - "constants $C_g$, $C'_g$ and $C''_g$ that depend only on $|g|_{\rm w}$" is read as: one triple of constants for each value $c$ of $|g|_{\rm w}$, serving every $g$ with $|g|_{\rm w} = c$.
--   - "For all $n$" is read as all integers $n \ge 1$.
--   - The paper defines $\eta(g, j, n)$ and $\vartheta(g, j, n)$ by series in the proof. The statement asserts reals $\eta$ and $\vartheta$ with the displayed equations and bounds. (2.vi) writes $\eta(g, n, j)$ and $\vartheta(g, n, j)$; this is read as the same $\eta(g, j, n)$ and $\vartheta(g, j, n)$, the arguments in the order of (2.v) and of the proof.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, pp. 779–780, Lemma 2.6

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem a_apply_div_a_expansion (c : ℝ) :
    ∃ C C' C'' : ℝ, ∀ g ∈ IntervalExchange.wobbling ℤ, wobblingNorm g = c →
      ∀ n : ℕ, 0 < n → ∀ j : ℤ, ∃ η ϑ : ℝ,
        a n (g j) / a n j = Real.exp (Real.exp (-(|j| : ℝ) / n) * ((|g j| : ℝ) - |j| + η)) ∧
        |η| ≤ C / n ∧
        a n (g j) / a n j - 1 =
          Real.exp (-(|j| : ℝ) / n) * ((|g j| : ℝ) - |j|) + η * Real.exp (-(|j| : ℝ) / n) + ϑ ∧
        |ϑ| ≤ C' * Real.exp (-2 * (|j| : ℝ) / n) ∧
        |a n (g j) / a n j - 1| ≤ C'' * Real.exp (-(|j| : ℝ) / n) := by
  sorry

end JuschenkoMonod
