-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedFiniteNestedSource_counts
-- name    : OAI.Erdos3.VectorPolynomial.preparedFiniteNestedSource_counts
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T08:03:58.904808+00:00
-- url     : https://prove2.me/theorems/93674629-e033-4797-9f08-7eaeefaf3ff5
-- title:
--   Kernel, coordinate, variable and layer counts of the nested source are below Bstruct
-- statement:
--   Let $m \in \mathbb N$, let $X_0, J_0$ be types, and let prep be a `RankPreparationFamily X₀ J₀ m` (a family of $m$ rank-preparation layers). Let $n_X, M, \mathrm{cutoff} \in \mathbb N$ and $B_{\mathrm{struct}} \in \mathbb R$; write $m' = \max(m, \mathrm{cutoff})$, $J_{\mathrm{alloc}} =$ `modularInitialBlockCount m' (nX + m' M)` (a natural number), and $\mathrm{prep}' =$ `prep.pad m'` (the family extended to $m'$ layers by empty layers). Assume every layer of prep has at most $M$ coordinates ($|(\mathrm{prep}\ j).\mathrm{Coord}| \le M$ for all $j$) and `enlargedPreparedCommonSamplerDimension m' M Jalloc` $\le B_{\mathrm{struct}}$. Then each of the following is at most $B_{\mathrm{struct}}$:
--
--   - the cardinality of `EnlargedPreparedCommonKernel m' Jalloc` $= \mathrm{Fin}((m'+1)(m'+3) + (m'+1)J_{\mathrm{alloc}})$;
--   - the cardinality of $\mathrm{Fin}\,n_X \oplus \Sigma_j\,(\mathrm{prep}'\ j).\mathrm{Coord}$;
--   - the cardinality of `LayerSamplerVariables (EnlargedPreparedCommonKernel m' Jalloc) (PreparedSamplerContinuous prep') (preparedSamplerTransverse prep') (EnlargedPreparedCommonSamplerBlock prep' Jalloc)`; and
--   - $m'$ itself.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedSource_counts` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteNestedSourceRelativeInitializerBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B187` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteNestedSourceRelativeInitializerBounds.lean#L266

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B187

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uα
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

section Source
variable {X₀ J₀ : Type} {m : ℕ} (prep : RankPreparationFamily X₀ J₀ m) (nX M : ℕ)
local notation "Jalloc" => modularInitialBlockCount m (nX + m * M)
local notation "Kernel" => EnlargedPreparedCommonKernel m Jalloc
local notation "Cont" => PreparedSamplerContinuous prep
local notation "Trans" => preparedSamplerTransverse prep
local notation "Blocks" => EnlargedPreparedCommonSamplerBlock prep Jalloc

end Source
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

theorem preparedFiniteNestedSource_counts
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M cutoff : ℕ) {Bstruct : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hnum : (enlargedPreparedCommonSamplerDimension (max m cutoff) M
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)) : ℝ) ≤ Bstruct) :
    (Fintype.card (EnlargedPreparedCommonKernel (max m cutoff)
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M))) : ℝ) ≤ Bstruct ∧
    (Fintype.card (Fin nX ⊕ (Σ j, (prep.pad (max m cutoff) j).Coord)) : ℝ) ≤ Bstruct ∧
    (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel (max m cutoff)
        (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)))
      (PreparedSamplerContinuous (prep.pad (max m cutoff)))
      (preparedSamplerTransverse (prep.pad (max m cutoff)))
      (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff))
        (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)))) : ℝ)
        ≤ Bstruct ∧ ((max m cutoff : ℕ) : ℝ) ≤ Bstruct := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
