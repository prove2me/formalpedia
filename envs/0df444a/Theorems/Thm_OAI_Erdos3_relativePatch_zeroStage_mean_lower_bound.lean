-- Prove2me | Theorems.Thm_OAI_Erdos3_relativePatch_zeroStage_mean_lower_bound
-- name    : OAI.Erdos3.relativePatch_zeroStage_mean_lower_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:57:23.209487+00:00
-- url     : https://prove2.me/theorems/39c6b52f-af4e-49ce-9289-6c630f8d5c23
-- title:
--   A positive patch score with no distinct weights forces rank zero and a mean gain
-- statement:
--   Let $X$ be a finite type with decidable equality and $s, d$ natural numbers. Let $N : X \to \mathbb N$ with $N_i > 0$ for all $i$, let $f : (X \to \mathbb Z) \to \mathbb R$, and let `patch : PolynomialPatch X s d` (a structure bundling weights $w : \mathrm{Fin}\,d \to \mathbb N$ with values in $[1, s]$ and monotone, polynomial slots, and a `PatchKernel d`, a Lipschitz function $\mathbb R^d \to [0,1]$; its value `patch.value` is a real function of $t : X \to \mathbb R$). Let $a$ and $\mathrm{surplus}$ be reals with $\mathrm{surplus} > 0$. Assume `relativePatchDistinctWeights patch` $\le 0$ (this is the number of distinct values of the weight function $w$) and
--   $$\mathrm{surplus} \le \mathrm{relativePatchBoxScore}(N, f, a, \mathrm{patch}) = \mathop{\mathbb E}_{x \in \mathrm{integerBox}\,N} (f(x) - a)\,\mathrm{patch.value}(x),$$
--   where `integerBox N` is the finite set of $x : X \to \mathbb Z$ with $0 \le x_i < N_i$ for all $i$. Then $d = 0$ and
--   $$a + \mathrm{surplus} \le \mathop{\mathbb E}_{x \in \mathrm{integerBox}\,N} \mathrm{relativeBoxInput}(N, f, x),$$
--   where `relativeBoxInput N f x` is $f(x)$ if $x \in$ `integerBox N` and $0$ otherwise.
--
--   Lean: `OAI.Erdos3.relativePatch_zeroStage_mean_lower_bound` in `lean/OAI/Combinatorics/Progressions/Estimates/CanonicalEmptyLayerGeometry.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1324` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/CanonicalEmptyLayerGeometry.lean#L396

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1324

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatch_zeroStage_mean_lower_bound
    {X : Type*} [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (f : (X → ℤ) → ℝ)
    (patch : PolynomialPatch X s d) {a surplus : ℝ}
    (hsurplus : 0 < surplus)
    (hstage : relativePatchDistinctWeights patch ≤ 0)
    (hscore : surplus ≤ relativePatchBoxScore N f a patch) :
    d = 0 ∧ a + surplus ≤ (𝔼 x ∈ integerBox N, relativeBoxInput N f x) := by
  sorry

end Erdos3
end
end OAI
