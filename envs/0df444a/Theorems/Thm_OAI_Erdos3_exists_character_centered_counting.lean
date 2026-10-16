-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_character_centered_counting
-- name    : OAI.Erdos3.exists_character_centered_counting
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:57:15.396983+00:00
-- url     : https://prove2.me/theorems/427b2573-d344-4283-9031-d1f75dc9c216
-- title:
--   Character-twisted centered progression counts are small for niltest-pseudorandom weights
-- statement:
--   Let $s \ge 1$ be a natural number and $\varepsilon > 0$ a real number. Then there exist a natural number $C \ge 2$ and a real number $\xi > 0$ with the following property. For every natural number $N \neq 0$ and every real $p \ge 2$ such that $N$ is odd and $e^{(p+2)^C} \le N$, and for every function $\mu : \mathbb Z/N \to \mathbb R$ with $0 \le \mu(x) \le e^{p}$ for all $x$ and $\mathbb E_{x \in \mathbb Z/N}\, \mu(x) = 1$ which satisfies `CyclicNiltestUpperComparison s N ((p+2)^C) (exp(-(p+2)^C)) μ (fun _ => 1 + ξ)` (with universe level $0$), and for every finite nonempty type $I$ with decidable equality and $|I| \le s+2$, every family of slopes $a : I \to \mathbb Z/N$ and every family of additive characters $\chi_i$ of $\mathbb Z/N$ (with values in $\mathbb C$) such that $a_i - a_j$ is a unit of $\mathbb Z/N$ whenever $i \neq j$, we have
--   $$\Bigl\| \mathbb E_{x \in \mathbb Z/N}\, \mathbb E_{d \in \mathbb Z/N} \prod_{i \in I} \chi_i(x + a_i d)\,\bigl(\mu(x + a_i d) - 1\bigr) \Bigr\| \le \varepsilon.$$
--   Here `CyclicNiltestUpperComparison degree N P ε f g` is OpenAI's predicate on two functions $f, g : \mathbb Z/N \to \mathbb R$: for every rational filtered nilmanifold `D` (over a Lie algebra in the given universe) of nilpotency degree at most `degree` and every niltest `T` on `D` (indexed by one coordinate of weight $1$) that is unit-interval-valued and has complexity at most $P$, one has $\mathbb E_{x \in \mathbb Z/N} (f(x) - g(x))\,\mathrm{Re}(\texttt{T.evalCyclic N}(x)) \le \varepsilon$.
--
--   Lean: `OAI.Erdos3.exists_character_centered_counting` in `lean/OAI/Combinatorics/Progressions/Fourier/CharacterCenteredCounting.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1325` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/CharacterCenteredCounting.lean#L55

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1325

namespace OAI

section

namespace Erdos3

open scoped TensorProduct NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_character_centered_counting (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ s + 2 →
      ∀ (slopes : I → ZMod N) (chi : I → AddChar (ZMod N) ℂ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ‖𝔼 x, 𝔼 d, ∏ i, chi i (x + slopes i * d) * ((mu (x + slopes i * d) - 1 : ℝ) : ℂ)‖ ≤
        epsilon := by
  sorry

end Erdos3
end
end OAI
