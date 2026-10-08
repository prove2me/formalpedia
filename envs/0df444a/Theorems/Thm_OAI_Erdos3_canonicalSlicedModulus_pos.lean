-- Prove2me | Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_pos
-- name    : OAI.Erdos3.canonicalSlicedModulus_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:23:44.250932+00:00
-- url     : https://prove2.me/theorems/1d52708d-c72b-4c00-8e7d-0486c35b7fd4
-- title:
--   The canonical sliced modulus is positive when all strides are
-- statement:
--   Let $\alpha,G,X$ be finite types ($\alpha$ with decidable equality), $L,M$ natural numbers, $\mathrm{selection} : \alpha\hookrightarrow G$ an embedding, $\mathrm{stride} : X\to\mathbb{N}$, and $\mathrm{height}$ a natural number. Assume $0<\mathrm{stride}(i)$ for every $i\in X$. Then for every $x : G\to$ `IntegerScalarCubeBox α L` (an `IntegerScalarCubeBox α L` is a function assigning to each element of $\mathrm{Option}\ \alpha$ an integer in $[-L,L)$), the natural number `canonicalSlicedModulus selection stride height x` (with $M$ as given) is positive. That natural number is defined to be $1$ unless $x$ satisfies `GoodScalarKernelTuple selection (1/M) M x`, in which case it is OpenAI's `residueRefinedPeriod` ($m\cdot\prod_{i\in X}\mathrm{stride}(i)$) of a kernel period candidate built from $x$ and $\mathrm{height}+1$.
--
--   Lean: `OAI.Erdos3.canonicalSlicedModulus_pos` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean#L29

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_pos (hs : ∀ i, 0 < stride i)
    (x : G → IntegerScalarCubeBox α L) :
    0 < canonicalSlicedModulus (M := M) selection stride height x := by
  sorry

end Erdos3
end
end OAI
