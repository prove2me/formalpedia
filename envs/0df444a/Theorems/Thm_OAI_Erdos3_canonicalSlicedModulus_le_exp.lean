-- Prove2me | Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_le_exp
-- name    : OAI.Erdos3.canonicalSlicedModulus_le_exp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:02:04.773983+00:00
-- url     : https://prove2.me/theorems/6c33cead-0aee-4603-befc-f03150456888
-- title:
--   The canonical sliced modulus is at most exp((height+1)P + |X|Q)
-- statement:
--   Let $\alpha,G,X$ be finite types ($\alpha$ with decidable equality), $L,M$ natural numbers, $\mathrm{selection} : \alpha\hookrightarrow G$ an embedding, $\mathrm{stride} : X\to\mathbb{N}$, and $\mathrm{height}$ a natural number. Let $P,Q$ be real numbers with $0\le P$, $0\le Q$, $M\le e^P$, and $\mathrm{stride}(i)\le e^Q$ for every $i\in X$. Then for every $x : G\to$ `IntegerScalarCubeBox α L` (functions from $\mathrm{Option}\ \alpha$ to integers in $[-L,L)$),
--   $$\texttt{canonicalSlicedModulus selection stride height } x\ \le\ \exp\big((\mathrm{height}+1)\,P+|X|\,Q\big),$$
--   where `canonicalSlicedModulus` (taken with this $M$) is the natural number that is $1$ unless $x$ satisfies `GoodScalarKernelTuple selection (1/M) M x`, and otherwise is OpenAI's `residueRefinedPeriod` ($m\cdot\prod_{i\in X}\mathrm{stride}(i)$) of a kernel period candidate built from $x$ and $\mathrm{height}+1$.
--
--   Lean: `OAI.Erdos3.canonicalSlicedModulus_le_exp` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean#L37

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_le_exp {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hM : (M : ℝ) ≤ Real.exp P) (hs : ∀ i, (stride i : ℝ) ≤ Real.exp Q)
    (x : G → IntegerScalarCubeBox α L) :
    (canonicalSlicedModulus (M := M) selection stride height x : ℝ) ≤
      Real.exp ((height + 1 : ℕ) * P + Fintype.card X * Q) := by
  sorry

end Erdos3
end
end OAI
