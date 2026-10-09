-- Prove2me | Theorems.Thm_OAI_Erdos3_primeCoordinateReference_weight_pos
-- name    : OAI.Erdos3.primeCoordinateReference_weight_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T18:10:57.967977+00:00
-- url     : https://prove2.me/theorems/f071eb1a-d831-4547-a636-320d8d827840
-- title:
--   Every prime-coordinate reference weight is positive
-- statement:
--   Let $\iota$ be a type, $\sigma$ a finite type with decidable equality, and $q : \iota \to \mathbb{N}$ with every $q_i \neq 0$. For $i \in \iota$ and $x : \sigma \to \mathbb{Z}/q_i$, the weight of $x$ under `primeCoordinateReference q i` is positive. Here `primeCoordinateReference q i` is OpenAI's uniform probability weights (a `FiniteProbabilityWeights`, OpenAI's structure bundling a probability weight function on a finite type) on $\sigma \to \mathbb{Z}/q_i$.
--
--   Lean: `OAI.Erdos3.primeCoordinateReference_weight_pos` in `lean/OAI/Combinatorics/Progressions/Lattices/AffineSampleAlphabet.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineSampleAlphabet.lean#L504

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

variable [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J G : Type*} [Fintype J] [AddCommGroup G] [Fintype G]

variable {q : ℕ} [NeZero q] [Module (ZMod q) G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]
  {p a : ℕ} [NeZero (p ^ a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

variable [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G] [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (p q a : ι → ℕ) [∀ i, NeZero (q i)] {G : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, Module (ZMod (q i)) (G i)] [∀ i, Fintype (G i)]
  (hp : ∀ i, (p i).Prime) (hcard : ∀ i, Fintype.card (G i) = p i ^ a i)

include hp hcard

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

universe u v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateReference_weight_pos {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (i : ι) (x : σ → ZMod (q i)) :
    0 < (primeCoordinateReference (σ := σ) q i).weight x := by
  sorry

end Erdos3
end
end OAI
