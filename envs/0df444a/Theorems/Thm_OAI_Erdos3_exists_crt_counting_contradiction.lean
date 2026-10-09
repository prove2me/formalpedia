-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_crt_counting_contradiction
-- name    : OAI.Erdos3.exists_crt_counting_contradiction
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T00:26:08.448983+00:00
-- url     : https://prove2.me/theorems/9023b007-40d5-45ee-be18-65bcd5db9f18
-- title:
--   A progression-free CRT input cannot pass the degree k-2 niltest comparison with 1 + xi
-- statement:
--   Let $J$ be a nonempty finite type and $k \ge 3$ a natural number. Then there exist a natural number $C \ge 2$ and a real number $\xi > 0$ such that the following holds. Let $N : J \to \mathbb{N}$ be pairwise coprime positive moduli with $M = \prod_j N_j$ (so $M > 0$), and let $\pi : \mathbb{Z}/M \to \prod_j \mathbb{Z}/N_j$ be the Chinese-remainder isomorphism `ZMod.prodEquivPi N hN`. Let $p \ge 2$ be real, and assume $M$ is odd, $\exp((p+2)^C) \le M$, $64k \le N_j$ for every $j$, and every natural $m$ with $1 \le m < k$ is a unit in $\mathbb{Z}/M$. Let $f : \prod_j \mathbb{Z}/N_j \to \mathbb{R}$ with $0 \le f \le e^{p}$ pointwise and $\mathbb{E}_{x \in \mathbb{Z}/M} f(\pi(x)) = 1$, and assume `IntegerVectorAPFree` $(\iota(\mathrm{supp}\, f))$ $k$, where $\iota$ = `residueBoxIntegerPoint N` sends $u$ to the integer vector $(\mathrm{val}(u_j))_j \in \mathbb{Z}^J$ and `IntegerVectorAPFree A k` means that for all $a, d \in \mathbb{Z}^J$ with $d \ne 0$ some $a + id$, $0 \le i < k$, lies outside $A$. Then `CyclicNiltestUpperComparison (k-2) M ((p+2)^C) (exp(-(p+2)^C)) (f ∘ π) (fun _ => 1 + ξ)` fails (at universe $0$), where `CyclicNiltestUpperComparison degree M P ε F G` is OpenAI's predicate: for every rational filtered nilmanifold of degree at most `degree` and every unit-interval-valued niltest $T$ of complexity at most $P$ on it, $\mathbb{E}_{x \in \mathbb{Z}/M}\,(F(x) - G(x))\,\mathrm{Re}\,T(x) \le \varepsilon$.
--
--   Lean: `OAI.Erdos3.exists_crt_counting_contradiction` in `lean/OAI/Combinatorics/Progressions/Lattices/AbsoluteCRTWindow.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B034` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AbsoluteCRTWindow.lean#L44

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_crt_counting_contradiction {J : Type*} [Fintype J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) {p : ℝ},
      2 ≤ p → Odd (∏ j, N j) → Real.exp ((p + 2) ^ C) ≤ (∏ j, N j) →
      (∀ j, 64 * k ≤ N j) →
      (∀ m : ℕ, 1 ≤ m → m < k → IsUnit (m : ZMod (∏ j, N j))) →
      ∀ f : ((j : J) → ZMod (N j)) → ℝ,
      (∀ u, 0 ≤ f u ∧ f u ≤ Real.exp p) →
      (𝔼 x : ZMod (∏ j, N j), f (ZMod.prodEquivPi N hN x)) = 1 →
      IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
      ¬ CyclicNiltestUpperComparison.{0} (k - 2) (∏ j, N j) ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (fun x => f (ZMod.prodEquivPi N hN x)) (fun _ => 1 + xi) := by
  sorry

end Erdos3
end
end OAI
