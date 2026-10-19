-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_native_partition_expansion_contradiction_s2
-- name    : OAI.Erdos3.exists_native_partition_expansion_contradiction_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:14:05.111823+00:00
-- url     : https://prove2.me/theorems/350a32f0-6779-4b33-bbe6-5b5d7366656f
-- title:
--   A shift family of positive niltests expanded through a partition contradicts a degree-(s+2) niltest upper comparison, given the degree-(s+1) shift comparison
-- statement:
--   Let $B, k, c, s$ be natural numbers with $c \ge 2$, and $\varepsilon$ a real number with $0 < \varepsilon < 1$. Fix universe levels $u$ and $v$. Assume `CyclicShiftComparison (s+1) (ε/2) c` with Lie algebras in universe $u$ (a proposition defined by OpenAI: for every nonzero natural number $N$ and real $p \ge 2$ with $N$ odd and $e^{(p+2)^c} \le N$, and all $f, g, J : \mathbb{Z}/N \to \mathbb{R}$ with values in $[0, e^p]$, if `CyclicNiltestUpperComparison (s+1) N ((p+2)^c) (exp(-(p+2)^c)) f g` holds then there is $E \subseteq \mathbb{Z}/N$ with $\#E \le e^{-p} N$ such that OpenAI's `CyclicNiltestShiftBound s N p (exp(-p)) (fun n => f n - (1 + ε/2) g n) J E` holds). Here `CyclicNiltestUpperComparison degree N P δ f g` means: for every rational filtered nilmanifold (OpenAI's `RationalFilteredNilmanifold L s' dim`, with $L$ a rational Lie algebra in universe $u$ and a Hausdorff topological vector space structure on $\mathbb{R} \otimes_{\mathbb{Q}} L$) with $s' \le \mathrm{degree}$ and every one-variable niltest $T$ on it with $[0,1]$-valued observable and complexity at most $P$, $\mathbb{E}_{x \in \mathbb{Z}/N}(f(x) - g(x)) \operatorname{Re} T(x) \le \delta$, where $T(x)$ denotes the niltest evaluated at the integer $x.\mathrm{val}$ (`evalCyclic`).
--
--   Then there is a natural number $a \ge 2$ such that for every natural number $C$ there is a natural number $D \ge 2$ with $a \le D$ and the following property. Let $L, M$ be rational Lie algebras in universe $u$, each with a topology on its real base change making it a Hausdorff topological vector space; let $d, e$ be natural numbers, $D_0$ a `RationalFilteredNilmanifold L (s+1) d` and $Q$ a `RationalFilteredNilmanifold M s e`. Let $N$ be a nonzero natural number, $I$ a finite type in universe $v$, $p, \sigma, \delta$ reals, $f, g, \mathrm{weight} : \mathbb{Z}/N \to \mathbb{R}$, $A : I \to \mathbb{Z}/N \to \mathbb{R}$, $H \subseteq \mathbb{Z}/N$ a finite set, $U(i, j, h)$ one-variable niltests on $Q$ for $i, j \in I$ and $h \in \mathbb{Z}/N$, $S(h)$ one-variable niltests on $D_0$ for $h \in \mathbb{Z}/N$, and $\mathrm{err} : \mathbb{Z}/N \to \mathbb{Z}/N \to \mathbb{R}$. Assume:
--   - $p \ge 2$, $N$ odd, $e^{(p+2)^D} \le N$, $\#I \le e^{(p+C)^C}$;
--   - $e^{-(p+2)^k} \le \sigma$ and $e^{-(p+2)^k} \le \delta$;
--   - $0 \le f(n) \le e^p$, $0 \le g(n) \le e^p$, $0 \le \mathrm{weight}(n) \le e^p$ for all $n$;
--   - for each $i$, `PositiveCyclicNiltest (s+2) N ((p+C)^C) (A i)` holds (OpenAI: $A_i(x) = \operatorname{Re} T(x)$ for all $x$, for some $[0,1]$-valued one-variable niltest $T$ of complexity at most $(p+C)^C$ on a rational filtered nilmanifold of degree at most $s+2$ with Lie algebra in universe $u$);
--   - every $U(i,j,h)$ is $[0,1]$-valued (its observable has zero imaginary part and real part in $[0,1]$) and has complexity at most $(p+C)^C$;
--   - $\sigma N \le \#H$, and $S(h)$ is $[0,1]$-valued for every $h \in H$;
--   - for every $h \in H$ and $n$: $\operatorname{Re} S(h)(n) = \sum_{i}\sum_{j} A_i(n)\, A_j(n+h) \operatorname{Re} U(i,j,h)(n) + \mathrm{err}(h, n)$;
--   - for every $h \in H$: $\mathbb{E}_n |\mathrm{err}(h, n)| \le e^{(p+B)^B} e^{-(p+2)^a} + 3/N$;
--   - `CyclicNiltestUpperComparison (s+2) N ((p+2)^D) (exp(-(p+2)^D)) f g` holds (universe $u$);
--   - for every $h \in H$: $\delta < \mathbb{E}_n\, (f(n) - (1+\varepsilon) g(n))\, \mathrm{weight}(n+h) \operatorname{Re} S(h)(n)$.
--
--   Then a contradiction follows (the conclusion is `False`).
--
--   Lean: `OAI.Erdos3.exists_native_partition_expansion_contradiction_s2`, which states OpenAI's `OAI.Erdos3.exists_native_partition_expansion_contradiction` (in `lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B142` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean (declaration OAI.Erdos3.exists_native_partition_expansion_contradiction)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B142

section

namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_partition_expansion_contradiction_s2 (B k c s : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{u} (s + 1) (epsilon / 2) c) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ C : ℕ, ∃ D : ℕ, 2 ≤ D ∧ a ≤ D ∧
      ∀ {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
        [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
        (D₀ : RationalFilteredNilmanifold L (s + 1) d) (Q : RationalFilteredNilmanifold M s e)
        (N : ℕ) [NeZero N] {I : Type v} [Fintype I] (p sigma delta : ℝ)
        (f g weight : ZMod N → ℝ) (A : I → ZMod N → ℝ) (H : Finset (ZMod N))
        (U : I → I → ZMod N → Q.Niltest (fun _ : Unit => 1))
        (S : ZMod N → D₀.Niltest (fun _ : Unit => 1)) (err : ZMod N → ZMod N → ℝ),
      2 ≤ p → Odd N → Real.exp ((p + 2) ^ D) ≤ N →
      (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) →
      Real.exp (-((p + 2) ^ k)) ≤ sigma → Real.exp (-((p + 2) ^ k)) ≤ delta →
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      (∀ i, PositiveCyclicNiltest.{u} (s + 2) N ((p + C) ^ C) (A i)) →
      (∀ i j h, (U i j h).UnitIntervalValued) →
      (∀ i j h, (U i j h).ComplexityLE ((p + C) ^ C)) →
      sigma * N ≤ (H.card : ℝ) → (∀ h ∈ H, (S h).UnitIntervalValued) →
      (∀ h ∈ H, ∀ n, ((S h).evalCyclic N (fun _ => n)).re =
        (∑ i, ∑ j, A i n * A j (n + h) * ((U i j h).evalCyclic N (fun _ => n)).re) + err h n) →
      (∀ h ∈ H, (𝔼 n, |err h n|) ≤
        Real.exp ((p + B) ^ B) * Real.exp (-((p + 2) ^ a)) + 3 / N) →
      CyclicNiltestUpperComparison.{u} (s + 2) N ((p + 2) ^ D)
        (Real.exp (-((p + 2) ^ D))) f g →
      (∀ h ∈ H, delta < 𝔼 n, (f n - (1 + epsilon) * g n) * weight (n + h) *
        ((S h).evalCyclic N (fun _ => n)).re) → False := by
  sorry

end Erdos3

end

end OAI
end
