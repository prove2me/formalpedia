-- Prove2me | Theorems.Thm_OAI_Erdos3_CellRefinement_matched_flat_integral_of_niltest_comparison
-- name    : OAI.Erdos3.CellRefinement.matched_flat_integral_of_niltest_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T00:26:27.484843+00:00
-- url     : https://prove2.me/theorems/429e5585-3391-4d0c-8201-40d90ea8cbbb
-- title:
--   A flat local convolution and a degree-one niltest comparison make the matched integral small
-- statement:
--   Let $N$ be a positive natural number, $L \subseteq \mathbb{Z}/N$ a finite set, and $S$ a `CyclicBohr.Set N` (OpenAI's structure of a finite set of frequencies in $\mathbb{Z}/N$ and a radius $\ge 0$, with carrier $\{x : |1 - e(rx/N)| \le \text{radius for all frequencies } r\}$ and rank the number of frequencies) that is rank-regular (OpenAI's predicate `IsRankRegular`) and has $S.\mathrm{radius} \le 1$. Let $A, B, f, g : \mathbb{Z}/N \to \mathbb{R}$ and $z \in \mathbb{Z}/N$. Let $u, v \in \mathbb{R}$ with $0 < u \le 1$ and $0 < v \le 1$, and let $\varepsilon, p, C, D, R, P, M \in \mathbb{R}$ with $0 < \varepsilon$, $1 \le p$, $0 \le C$, $0 \le D$, $0 \le R$, $0 \le M$, $M \le e^{Cp}$ and $e^{-R} \le S.\mathrm{radius}$. Let $q$ be a positive natural number with $(1 + C + (D+1) + \log 3)\,p \le q \log 2$. Assume $0 \le A, B \le e^{p}$ pointwise; $f \ge 0$ and $g \ge 0$ pointwise; $g(x)/v \le M$ for all $x$; $f$ vanishes off $L$ and its average over $L$ equals $u$; and
--   $$\Bigl(\mathbb{E}_{s, t \in S.\mathrm{carrier}} \bigl|\phi(s+t) - 1\bigr|^q\Bigr)^{1/q} \le \texttt{flatComparisonDelta}\ \varepsilon = \frac{\varepsilon}{4(2+\varepsilon)},$$
--   where $\phi(t) = |L|^{-1}\sum_{x \in \mathbb{Z}/N} (f(x)/u)(g(t-x)/v)$ (this is `LocalConvolution.sumLp` applied to `LocalConvolution.convolution`). Assume further $2 S.\mathrm{rank} + p + (D+2)p + R + 1612 \le P$, $(D+2)p + 2 + S.\mathrm{rank}(R + 10) \le P$, and `CyclicNiltestUpperComparison 1 N P (exp(-P)) A B` (at universe $0$: for every rational filtered nilmanifold of degree at most $1$ and every unit-interval-valued niltest $T$ of complexity at most $P$ on it, the average over $\mathbb{Z}/N$ of $(A(x) - B(x))\,\mathrm{Re}\,T(x)$ is at most $e^{-P}$). Then
--   $$\texttt{matchedIntegral}\ L\ S.\mathrm{carrier}\ a\ f\ g \le e^{-Dp}(uv)^{1/4},$$
--   where $a(x) = A(z+x) - (1+\varepsilon)B(z+x)$ and `matchedIntegral L S a f g` is the average over $r \in L$ and $s, t \in S$ of $f(r)\,g(-r+s+t)\,a(s+t)$.
--
--   Lean: `OAI.Erdos3.CellRefinement.matched_flat_integral_of_niltest_comparison` in `lean/OAI/Combinatorics/Progressions/Nilpotent/MatchedFlatNiltest.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B034` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Nilpotent/MatchedFlatNiltest.lean#L14

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034

namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {N : ℕ} [NeZero N]

theorem matched_flat_integral_of_niltest_comparison
    (L : Finset (ZMod N)) (S : CyclicBohr.Set N)
    (hS : S.IsRankRegular) (hS1 : S.radius ≤ 1)
    (A B f g : ZMod N → ℝ) (z : ZMod N)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1)
    {epsilon p C D R P M : ℝ} (hepsilon : 0 < epsilon) (hp : 1 ≤ p)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hMcap : M ≤ Real.exp (C * p)) (hwidth : Real.exp (-R) ≤ S.radius)
    {q : ℕ} (hq : 0 < q)
    (horder : (1 + C + (D + 1) + Real.log 3) * p ≤ (q : ℝ) * Real.log 2)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ Real.exp p)
    (hB : ∀ x, 0 ≤ B x ∧ B x ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hgcap : ∀ x, g x / v ≤ M)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hfmean : (𝔼 x ∈ L, f x) = u)
    (hflat : LocalConvolution.sumLp S.carrier
      (fun x => LocalConvolution.convolution L (fun y => f y / u) (fun y => g y / v) x - 1) q ≤
        flatComparisonDelta epsilon)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B) :
    matchedIntegral L S.carrier (fun x => A (z + x) - (1 + epsilon) * B (z + x)) f g ≤
      Real.exp (-(D * p)) * (u * v) ^ (1 / 4 : ℝ) := by
  sorry

end Erdos3.CellRefinement
end
end OAI
