-- Prove2me | Theorems.Thm_OAI_Erdos3_PositiveShiftBasis_exists_bounded_native_contradiction_s2
-- name    : OAI.Erdos3.PositiveShiftBasis.exists_bounded_native_contradiction_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:30:38.874776+00:00
-- url     : https://prove2.me/theorems/acbf9a03-4433-4466-9427-14dbddf64ba4
-- title:
--   A positive shift basis with an adapted weight grading contradicts a degree-(s+2) niltest upper comparison, given the degree-(s+1) shift comparison
-- statement:
--   Let $s, c$ be natural numbers with $c \ge 2$, and let $\varepsilon$ be a real number with $0 < \varepsilon < 1$. Assume `CyclicShiftComparison (s+1) (ε/2) c` (a proposition defined by OpenAI, with the Lie algebras involved taken in the lowest universe `Type`). It says: for every nonzero natural number $N$ and real $p$ with $p \ge 2$, $N$ odd and $e^{(p+2)^c} \le N$, and all $f, g, J : \mathbb{Z}/N \to \mathbb{R}$ with values in $[0, e^p]$, if `CyclicNiltestUpperComparison (s+1) N ((p+2)^c) (exp(-(p+2)^c)) f g` holds, then there is a set $E \subseteq \mathbb{Z}/N$ with $\#E \le e^{-p} N$ such that OpenAI's `CyclicNiltestShiftBound s N p (exp(-p)) (fun n => f n - (1 + ε/2) * g n) J E` holds. Here `CyclicNiltestUpperComparison degree N P δ f g` (defined by OpenAI) means: for every rational filtered nilmanifold $D$ (OpenAI's `RationalFilteredNilmanifold L s' dim`, on a rational Lie algebra $L$ in `Type` with a topology on $\mathbb{R} \otimes_{\mathbb{Q}} L$ making it a Hausdorff topological vector space) with $s' \le \mathrm{degree}$, and every niltest $T$ on $D$ in one variable (`D.Niltest (fun _ : Unit => 1)`) whose observable takes values in $[0,1]$ and which has complexity at most $P$, the average over $x \in \mathbb{Z}/N$ of $(f(x) - g(x)) \cdot \operatorname{Re} T(x)$ is at most $\delta$, where $T(x)$ is the niltest evaluated at the integer $x.\mathrm{val}$ (`T.evalCyclic`).
--
--   Then there is a natural number $C \ge 2$ with the following property. Let $N$ be a nonzero natural number, $q$ a real number, $f, g, J : \mathbb{Z}/N \to \mathbb{R}$, and let $B$ be a `PositiveShiftBasis (s+1) N q a J` with $a(n) = f(n) - (1+\varepsilon) g(n)$ (a structure defined by OpenAI, with its Lie algebra in `Type`: it packages a rational filtered nilmanifold `B.model` of degree $s+1$ and dimension `B.dim`, with geometric complexity at most $q$, a set of at least $e^{-q} N$ shifts $h$, and for each such shift rational frequencies, mode niltests correlating with $n \mapsto a(n) J(n+h)$ beyond $e^{-q}$, and a $[0,1]$-valued test niltest invariant under the vertical directions killed by the frequencies with $\mathbb{E}_n\, a(n) J(n+h) \operatorname{Re} T_h(n) > e^{-q}$). Let $w : \operatorname{Fin}(B.\mathrm{dim}) \to \mathbb{N}$ be such that for every $k$ the $k$-th layer of the filtration of `B.model` equals the $\mathbb{Q}$-span of the basis vectors `B.model.basis i` with $k \le w(i)$. Let $p$ be a real number with $2 \le p$ and $q \le p$, and assume $N$ is odd, $e^{(p+C)^C} \le N$, and $0 \le f(n) \le e^p$, $0 \le g(n) \le e^p$, $0 \le J(n) \le e^p$ for all $n$. Then `CyclicNiltestUpperComparison (s+2) N ((p+C)^C) (exp(-(p+C)^C)) f g` (with Lie algebras in `Type`) is false.
--
--   Lean: `OAI.Erdos3.PositiveShiftBasis.exists_bounded_native_contradiction_s2`, which states OpenAI's `OAI.Erdos3.PositiveShiftBasis.exists_bounded_native_contradiction` (in `lean/OAI/Combinatorics/Progressions/Estimates/AxisCompression.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B161` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AxisCompression.lean (declaration OAI.Erdos3.PositiveShiftBasis.exists_bounded_native_contradiction)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161

section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

namespace PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_bounded_native_contradiction_s2 (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {f g J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f n - (1 + epsilon) * g n) J)
      (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f g → False := by
  sorry

end PositiveShiftBasis
end Erdos3

end

end OAI
end
