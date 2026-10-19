-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_positiveGrid_compression_bound_s2
-- name    : OAI.Erdos3.exists_positiveGrid_compression_bound_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:25.914204+00:00
-- url     : https://prove2.me/theorems/463aea18-0131-440b-91d3-1c5324637275
-- title:
--   Compression bound for positive grid means of functions dominated by g against niltests
-- statement:
--   Let $s \ge 1$ be a natural number and $\varepsilon$ a real number with $0 < \varepsilon < 1$. Then there is a natural number $C \ge 2$ with the following property.
--
--   Let $j$ be a natural number, $N$ a nonzero natural number, and $p, L, g, A$ real numbers with $p \ge 2$, $L \ge 2$, $1 \le g \le e^{p}$, $A \ge 0$, $N$ odd, and $e^{(p + L + 2)^C} \le N$. Put $Q = (p + L + 2)^C$. Let $a : \mathrm{Fin}(j + 1) \to \mathbb{N}$ with $a_0 \le p$, and write $a'$ for the tail $i \mapsto a_{i+1}$ on $\mathrm{Fin}\ j$. For $b : \mathrm{Fin}\ \ell \to \mathbb{N}$, let a vertex of the grid $b$ (an element of `PositiveGridVertex b`) be an element of $\prod_i \mathrm{Fin}(b_i)$, let `positiveGridVolume b` $= \prod_i b_i$, and for $h$ assigning to each vertex a function $\mathbb{Z}/N \to \mathbb{R}$ let
--   $$\texttt{positiveGridMean}\ b\ h = \mathbb{E}_{t}\ \prod_{v} h_v\Bigl(\sum_i t_i(v_i)\Bigr),$$
--   the average being over all $t$ with $t_i : \mathrm{Fin}(b_i) \to \mathbb{Z}/N$ (definitions by OpenAI). Say that `CyclicNiltestUpperComparison d N P ε' f₁ f₂` holds (a predicate defined by OpenAI) if for every rational filtered nilmanifold of step at most $d$ and every unit-interval-valued niltest $T$ on it of complexity at most $P$, $\mathbb{E}_{x \in \mathbb{Z}/N} (f_1(x) - f_2(x))\cdot \mathrm{Re}\,T(x) \le \varepsilon'$.
--
--   Let $f$ assign to each vertex $v$ of the grid $a$ a function $f_v : \mathbb{Z}/N \to \mathbb{R}$, and suppose:
--   - $0 \le f_v(x) \le e^{p}$ for all $v, x$;
--   - for every vertex $v$, `CyclicNiltestUpperComparison s N Q (exp(-Q)) (f v) (fun _ => g)` holds;
--   - for every $h$ assigning to each vertex $v$ of the grid $a'$ a function $h_v : \mathbb{Z}/N \to \mathbb{R}$ with $0 \le h_v(x) \le e^{p^2}$ for all $v, x$ and with `CyclicNiltestUpperComparison (s - 1) N L (exp(-L)) (h v) (fun _ => 1)` for every $v$, one has `positiveGridMean a' h` $\le A$.
--
--   Then
--   $$\texttt{positiveGridMean}\ a\ f \le \bigl((1 + \varepsilon) g\bigr)^{\texttt{positiveGridVolume}\ a}\cdot A + e^{(\texttt{positiveGridVolume}\ a)\cdot p}\cdot \texttt{positiveGridVolume}\ a'\cdot e^{-L}.$$
--   (The niltest comparisons are taken at universe level $0$.)
--
--   Lean: `OAI.Erdos3.exists_positiveGrid_compression_bound_s2`, which states OpenAI's `OAI.Erdos3.exists_positiveGrid_compression_bound` (in `lean/OAI/Combinatorics/Progressions/Sampling/PositiveGridFamily.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B028`, `OAIE3v2B130` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PositiveGridFamily.lean (declaration OAI.Erdos3.exists_positiveGrid_compression_bound)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B028
import Definitions.Def_OAIE3v2B130

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_positiveGrid_compression_bound_s2 (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {j N : ℕ} [NeZero N] {p L g A : ℝ},
      2 ≤ p → 2 ≤ L → 1 ≤ g → g ≤ Real.exp p → 0 ≤ A → Odd N →
      Real.exp ((p + L + 2) ^ C) ≤ N →
      ∀ (a : Fin (j + 1) → ℕ), (a 0 : ℝ) ≤ p →
      ∀ f : PositiveGridVertex a → ZMod N → ℝ,
      (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
      (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
        (Real.exp (-((p + L + 2) ^ C))) (f b) (fun _ => g)) →
      (∀ h : PositiveGridVertex (fun i => a i.succ) → ZMod N → ℝ,
        (∀ b x, 0 ≤ h b x ∧ h b x ≤ Real.exp (p ^ 2)) →
        (∀ b, CyclicNiltestUpperComparison.{0} (s - 1) N L (Real.exp (-L)) (h b) (fun _ => 1)) →
        positiveGridMean (fun i => a i.succ) h ≤ A) →
      positiveGridMean a f ≤ ((1 + epsilon) * g) ^ positiveGridVolume a * A +
        Real.exp ((positiveGridVolume a : ℝ) * p) *
          (positiveGridVolume (fun i => a i.succ) : ℝ) * Real.exp (-L) := by
  sorry

end Erdos3

end

end OAI
end
