-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_scored_cyclic_patch_s2
-- name    : OAI.Erdos3.exists_scored_cyclic_patch_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:22.58571+00:00
-- url     : https://prove2.me/theorems/439363f5-281f-4a70-9451-afe2bad920ac
-- title:
--   A positive cyclic nilsequence test with a large weighted average can be replaced by a polynomial patch of polynomial cost
-- statement:
--   Let $s$ be a natural number. Then there is a natural number $C \ge 2$ with the following property. Let $N$ be a nonzero natural number, $X$ a finite type, $T : \mathbb{Z}/N\mathbb{Z} \to \mathbb{R}$, $a : X \to \mathbb{R}$, $n : X \to \mathbb{Z}/N\mathbb{Z}$, and $p \ge 0$ a real number. Suppose that `PositiveCyclicNiltest s N p T` holds (a proposition defined by OpenAI, at the universe level $u$ of the statement: $T$ is the real part of the cyclic evaluation $x \mapsto$ `T'.evalCyclic N x` of a niltest `T'` on some rational filtered nilmanifold of degree at most $s$, where `T'` is unit-interval valued and has complexity at most $p$), and that
--   $$e^{-p} \le \mathbb{E}_{x \in X}\, a(x)\, T(n(x)).$$
--   Then there exist a natural number $d$ and a polynomial patch $P$ (an OpenAI `PolynomialPatch Unit s d`: a patch in one real variable with $d$ slots of weights between $1$ and $s$ and a Lipschitz kernel, whose value `P.value t` lies in $[0,1]$) such that
--   $$d + \log\bigl(2 + \operatorname{lip}(P)\bigr) \le (p+2)^{C}$$
--   where $\operatorname{lip}(P)$ is the Lipschitz constant recorded in the kernel of $P$, and
--   $$e^{-(p+2)^{C}} \le \mathbb{E}_{x \in X}\, a(x)\, P.\mathrm{value}\bigl(\mathrm{val}(n(x))\bigr),$$
--   where $\mathrm{val}(n(x)) \in \{0, \dots, N-1\}$ is the canonical representative of $n(x)$, read as a real number.
--
--   Lean: `OAI.Erdos3.exists_scored_cyclic_patch_s2`, which states OpenAI's `OAI.Erdos3.exists_scored_cyclic_patch` (in `lean/OAI/Combinatorics/Progressions/Polynomial/ScoredCyclicPolynomialPatch.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B142` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/ScoredCyclicPolynomialPatch.lean (declaration OAI.Erdos3.exists_scored_cyclic_patch)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B142

section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem exists_scored_cyclic_patch_s2 (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {X : Type*} [Fintype X]
      (T : ZMod N → ℝ) (a : X → ℝ) (n : X → ZMod N) {p : ℝ},
      0 ≤ p → PositiveCyclicNiltest.{u} s N p T →
      Real.exp (-p) ≤ (𝔼 x, a x * T (n x)) →
      ∃ d : ℕ, ∃ P : PolynomialPatch Unit s d,
        (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤ (𝔼 x, a x * P.value (fun _ => ((n x).val : ℝ))) := by
  sorry

end Erdos3

end

end OAI
end
