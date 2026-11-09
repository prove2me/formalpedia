-- Prove2me | Theorems.Thm_IntADSat_lemma_B_3
-- name    : IntADSat.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:42.093299+00:00
-- url     : https://prove2.me/theorems/58ed4bd6-6390-41cd-8fb6-e1ae9563dc18
-- title:
--   Lemma B.3 — binomial point and tail exponents
-- statement:
--   Fix $a>0$ and let $\log$ be the natural logarithm. Suppose $N=n+O(\sqrt n)$ and
--
--   $$
--   u=\frac N2-a\sqrt{n\log n}+O(\sqrt n).
--   $$
--
--   Then
--
--   $$
--   \Pr[\mathrm{Bin}(N,1/2)=\lfloor u\rfloor]=n^{-1/2-2a^2+o(1)},\qquad \Pr[\mathrm{Bin}(N,1/2)\le\lfloor u\rfloor]=n^{-2a^2+o(1)} .
--   $$
--
--   The error is uniform when the constants in the two $O(\sqrt n)$ terms are bounded. The analogous upper-tail estimates hold by symmetry: for $u'=N/2+a\sqrt{n\log n}+O(\sqrt n)$, $\Pr[\mathrm{Bin}(N,1/2)=\lceil u'\rceil]=n^{-1/2-2a^2+o(1)}$ and $\Pr[\mathrm{Bin}(N,1/2)\ge\lceil u'\rceil]=n^{-2a^2+o(1)}$.
--
--   Precisely: for every $C\ge0$ and $\delta>0$ there is $n_0$ such that for all $n\ge n_0$, all $N$ with $|N-n|\le C\sqrt n$ and all $u$ (resp. $u'$) within $C\sqrt n$ of $N/2-a\sqrt{n\log n}$ (resp. $N/2+a\sqrt{n\log n}$), each of the four probabilities lies between $n^{E-\delta}$ and $n^{E+\delta}$, with $E=-1/2-2a^2$ for the point probabilities and $E=-2a^2$ for the tails.
--
--   Differences from the source:
--   - reading: o(1) errors, uniform when the constants in the two O(√n) terms are bounded → ∀ C ≥ 0, ∀ δ > 0, eventually in n, for all N, u with |N − n| ≤ C√n and |u − (N/2 − a√(n log n))| ≤ C√n, two-sided bounds n^(E∓δ); reason: uniformity over N and u is the content of the sentence; C bounds both constants
--   - reading: the analogous upper-tail estimates hold by symmetry → for u' within C√n of N/2 + a√(n log n): Pr[Bin = ⌈u'⌉] and Pr[Bin ≥ ⌈u'⌉] satisfy the same two-sided bounds; reason: mirror image j ↦ N − j of the lower-tail statement (⌈N − u⌉ = N − ⌊u⌋)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.3, p.15 (PDF 16)

import Mathlib
import Definitions.Def_QuasiPolyTrace_bin
import Definitions.Def_IntADSat_binomLE
import Definitions.Def_IntADSat_binomGE

set_option autoImplicit false

namespace IntADSat

/-- **Lemma B.3** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.15 (PDF 16)). Fix `a > 0`. If `N = n + O(√n)` and
`u = N/2 − a√(n log n) + O(√n)`, then `Pr[Bin(N, 1/2) = ⌊u⌋] = n^{−1/2−2a²+o(1)}` and
`Pr[Bin(N, 1/2) ≤ ⌊u⌋] = n^{−2a²+o(1)}`, uniformly when the constants in the two `O(√n)` terms are
bounded; the analogous upper-tail estimates hold by symmetry.

**Formalization Note** "The error is uniform when the constants are bounded" is read as: for every
bound `C ≥ 0` on both constants and every `δ > 0`, for all large `n`, every `N` and `u` within `C√n` of
`n` and of `N/2 − a√(n log n)` satisfy all bounds with exponent error at most `δ`. The upper tail is the
mirror: `u' = N/2 + a√(n log n) + O(√n)`, with `Pr[Bin = ⌈u'⌉]` and `Pr[Bin ≥ ⌈u'⌉]`. `log` is natural. -/
theorem lemma_B_3 (a : ℝ) (ha : 0 < a) (C : ℝ) (hC : 0 ≤ C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ N : ℕ, |(N : ℝ) - n| ≤ C * Real.sqrt n →
      (∀ u : ℝ, |u - ((N : ℝ) / 2 - a * Real.sqrt (n * Real.log n))| ≤ C * Real.sqrt n →
        (n : ℝ) ^ (-(1 / 2 : ℝ) - 2 * a ^ 2 - δ) ≤ QuasiPolyTrace.bin N ⌊u⌋ (1 / 2) ∧
        QuasiPolyTrace.bin N ⌊u⌋ (1 / 2) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ) - 2 * a ^ 2 + δ) ∧
        (n : ℝ) ^ (-2 * a ^ 2 - δ) ≤ binomLE N ⌊u⌋ ∧
        binomLE N ⌊u⌋ ≤ (n : ℝ) ^ (-2 * a ^ 2 + δ)) ∧
      (∀ u : ℝ, |u - ((N : ℝ) / 2 + a * Real.sqrt (n * Real.log n))| ≤ C * Real.sqrt n →
        (n : ℝ) ^ (-(1 / 2 : ℝ) - 2 * a ^ 2 - δ) ≤ QuasiPolyTrace.bin N ⌈u⌉ (1 / 2) ∧
        QuasiPolyTrace.bin N ⌈u⌉ (1 / 2) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ) - 2 * a ^ 2 + δ) ∧
        (n : ℝ) ^ (-2 * a ^ 2 - δ) ≤ binomGE N ⌈u⌉ ∧
        binomGE N ⌈u⌉ ≤ (n : ℝ) ^ (-2 * a ^ 2 + δ)) := by sorry

end IntADSat
