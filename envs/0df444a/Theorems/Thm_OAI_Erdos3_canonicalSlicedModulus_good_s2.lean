-- Prove2me | Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_good_s2
-- name    : OAI.Erdos3.canonicalSlicedModulus_good_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:42:46.411856+00:00
-- url     : https://prove2.me/theorems/83177e17-574b-4ef2-be9c-25afc580bd67
-- title:
--   On a good scalar kernel tuple the canonical sliced modulus equals the residue-refined kernel period
-- statement:
--   Let $\alpha$ (finite, with decidable equality), $G$ and $X$ be finite types, $L, M, \mathrm{height}$ natural numbers, `selection` $: \alpha \hookrightarrow G$ an embedding and $\mathrm{stride} : X \to \mathbb{N}$. Let $x : G \to$ `IntegerScalarCubeBox α L` (an `IntegerScalarCubeBox α L` is a map from `Option α` to integers in $[-L, L)$), and assume `GoodScalarKernelTuple selection (1/M) M x` holds (OpenAI: the normalized scalar cube minor of $x$ at `selection` has absolute value greater than $1/M$, and the range of the scalar cube difference matrix of $x$ has a bounded scalar period, at most $M$; call this proof $hx$).
--
--   Then
--   $$\texttt{canonicalSlicedModulus selection stride height}\ x = \texttt{residueRefinedPeriod}\bigl(\texttt{kernelPeriodCandidate}(\mathrm{height} + 1, \texttt{goodKernelUniformCandidate selection x hx height}),\ \mathrm{stride}\bigr),$$
--   where, by OpenAI's definitions, `canonicalSlicedModulus` (with parameter $M$) is the right-hand side when $x$ is good and $1$ otherwise, `goodKernelUniformCandidate` is an element $a \in \{0, \dots, M-1\}$ chosen from the period witness in $hx$, `kernelPeriodCandidate d a` $= (a + 1)^d$, and `residueRefinedPeriod m q` $= m \cdot \prod_{d \in X} q(d)$.
--
--   Lean: `OAI.Erdos3.canonicalSlicedModulus_good_s2`, which states OpenAI's `OAI.Erdos3.canonicalSlicedModulus_good` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B113` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean (declaration OAI.Erdos3.canonicalSlicedModulus_good)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B113

section

namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_good_s2 (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) :
    canonicalSlicedModulus (M := M) selection stride height x =
      residueRefinedPeriod (kernelPeriodCandidate (height + 1)
        (goodKernelUniformCandidate selection x hx height)) stride := by
  sorry

end Erdos3

end

end OAI
end
