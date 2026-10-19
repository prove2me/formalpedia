-- Prove2me | Theorems.Thm_OAI_SeparableQuotient_InfiniteRamsey_homogeneous_subset
-- name    : OAI.SeparableQuotient.InfiniteRamsey.homogeneous_subset
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T20:46:49.548981+00:00
-- url     : https://prove2.me/theorems/8fd4ec0f-cedf-4e68-9aed-3cfd161c0ef9
-- title:
--   The infinite Ramsey theorem (Ramsey 1930): every finite coloring of the n-element subsets of an infinite set of naturals has an infinite homogeneous subset
-- statement:
--   Let $\chi$ be a finite set of colors (`χ : Type*` with `[Finite χ]`), let $n \in \mathbb{N}$, and let $c$ (`c : Finset ℕ → χ`) be a coloring of the finite subsets of $\mathbb{N}$ (only its values on $n$-element sets matter). Let $A \subseteq \mathbb{N}$ be infinite (`hA : A.Infinite`). Then there are a set $M \subseteq A$ and a color $b \in \chi$ such that $M$ is infinite and every $n$-element finite set $s$ with $s \subseteq M$ has color $c(s) = b$:
--   $$\exists\, M \subseteq A,\ M \text{ infinite},\ \exists\, b \in \chi:\quad \forall s \in [M]^n,\ \ c(s) = b .$$
--
--   This is the infinite Ramsey theorem, relative to an arbitrary infinite subset of the natural numbers. For $n = 0$ it is trivial (the empty set has a color), and for $n = 1$ it is the infinite pigeonhole principle.
--
--   Lean: `OAI.SeparableQuotient.InfiniteRamsey.homogeneous_subset`, OpenAI's theorem of that name in `lean/OAI/Analysis/SeparableQuotients/RamseyThinning.lean`. The statement uses only Mathlib.
-- source:
--   F. P. Ramsey, On a problem of formal logic, Proc. London Math. Soc. (2) 30 (1930), 264–286 (the infinite Ramsey theorem). Lean proof: OpenAI, Relative independence of the separable quotient problem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 323; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SeparableQuotients/RamseyThinning.lean (declaration OAI.SeparableQuotient.InfiniteRamsey.homogeneous_subset)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.InfiniteRamsey
open Filter
open scoped Classical

variable {χ : Type*} [Finite χ]

theorem homogeneous_subset (n : ℕ) (c : Finset ℕ → χ) (A : Set ℕ) (hA : A.Infinite) :
    ∃ (M : Set ℕ) (b : χ), M ⊆ A ∧ M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  sorry

end SeparableQuotient.InfiniteRamsey

end

end OAI
end
