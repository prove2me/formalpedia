-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_configuration_centered_counting_s2
-- name    : OAI.Erdos3.exists_configuration_centered_counting_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:46:29.592179+00:00
-- url     : https://prove2.me/theorems/cb5282b2-6dbc-4d22-946b-c8565d66cf41
-- title:
--   Twisted centered configuration counts are small for a bounded density whose niltest correlations are dominated by a constant
-- statement:
--   Let $s \ge 1$ be a natural number and $\varepsilon > 0$ a real number. Then there are a natural number $C \ge 2$ and a real number $\xi > 0$ with the following property. Let $N$ be a nonzero natural number and $p \ge 2$ a real number with $N$ odd and $e^{(p+2)^C} \le N$. Let $\mu : \mathbb{Z}/N \to \mathbb{R}$ satisfy $0 \le \mu(x) \le e^p$ for all $x$ and $\mathbb{E}_{x \in \mathbb{Z}/N}\, \mu(x) = 1$, and assume `CyclicNiltestUpperComparison s N ((p+2)^C) (exp(-(p+2)^C)) μ (fun _ => 1 + ξ)` (defined by OpenAI, with Lie algebras in the lowest universe `Type`): for every rational filtered nilmanifold $D$ (OpenAI's `RationalFilteredNilmanifold L s' dim`, $L$ a rational Lie algebra with a Hausdorff topological vector space structure on $\mathbb{R} \otimes_{\mathbb{Q}} L$) with $s' \le s$, and every one-variable niltest $T$ on $D$ whose observable takes values in $[0,1]$ and which has complexity at most $(p+2)^C$, one has $\mathbb{E}_{x \in \mathbb{Z}/N}\, (\mu(x) - (1+\xi)) \operatorname{Re} T(x) \le e^{-(p+2)^C}$, where $T(x)$ is the niltest evaluated at the integer $x.\mathrm{val}$. Then for every nonempty finite type $I$ (in `Type`, with decidable equality) with $\#I \le s+2$, every $\mathrm{slopes} : I \to \mathbb{Z}/N$ such that $\mathrm{slopes}(i) - \mathrm{slopes}(j)$ is a unit of $\mathbb{Z}/N$ whenever $i \ne j$, and every additive character $\Psi$ of $\mathbb{Z}/N \times \mathbb{Z}/N$ with values in $\mathbb{C}$,
--   $$\Bigl\| \mathbb{E}_{x \in \mathbb{Z}/N}\, \mathbb{E}_{d \in \mathbb{Z}/N}\, \Psi(x, d) \prod_{i \in I} \bigl(\mu(x + \mathrm{slopes}(i)\, d) - 1\bigr) \Bigr\| \le \varepsilon.$$
--
--   Lean: `OAI.Erdos3.exists_configuration_centered_counting_s2`, which states OpenAI's `OAI.Erdos3.exists_configuration_centered_counting` (in `lean/OAI/Combinatorics/Progressions/Estimates/ConfigurationCenteredCounting.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B130` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ConfigurationCenteredCounting.lean (declaration OAI.Erdos3.exists_configuration_centered_counting)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B130

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_configuration_centered_counting_s2 (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ s + 2 →
      ∀ (slopes : I → ZMod N), (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ∀ Psi : AddChar (ZMod N × ZMod N) ℂ,
      ‖𝔼 x, 𝔼 d, Psi (x, d) * (∏ i, ((mu (x + slopes i * d) - 1 : ℝ) : ℂ))‖ ≤ epsilon := by
  sorry

end Erdos3

end

end OAI
end
