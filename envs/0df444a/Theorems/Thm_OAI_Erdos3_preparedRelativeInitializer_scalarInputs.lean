-- Prove2me | Theorems.Thm_OAI_Erdos3_preparedRelativeInitializer_scalarInputs
-- name    : OAI.Erdos3.preparedRelativeInitializer_scalarInputs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:31:26.842416+00:00
-- url     : https://prove2.me/theorems/b752a77e-2e4c-4580-bbac-8f36742a4ef8
-- title:
--   Scalar inputs for the prepared relative initializer follow from explicit budget bounds
-- statement:
--   Let $n_X, s, D, E, m, n_0, d_0$ be natural numbers, let `oldPatch : PolynomialPatch (Fin nX) s (D + E)` be a polynomial patch (a structure bundling weights, polynomial forms and a kernel), let `prep : RankPreparationFamily (Fin nX) (Fin D) m` be a family of $m$ rank-preparation layers, and let $p, p_{\mathrm{rel}}, \mathrm{precisionBudget}, a, \Lambda$ be real numbers. Assume: $2 \le p$; $m \le s$; for every $j$ the layer `prep j` has at most `preparationCoordinateCap m D (m * D)` coordinates; writing $M = $ `preparationCoordinateCap s D (s * D)`, $J_{\mathrm{alloc}} = $ `modularInitialBlockCount s (nX + s * M)` and $\mathrm{dim} = $ `enlargedPreparedCommonSamplerDimension s M Jalloc` (natural numbers defined by OpenAI), each of $p$, $s + 3$, $M$, $J_{\mathrm{alloc}}$, $\mathrm{dim}$ and `allocatedUniformChartLog M` $+\,1$ is at most $p_{\mathrm{rel}}$, where `allocatedUniformChartLog x` $= 20\,(x+1)^3$; $3p_{\mathrm{rel}} + 130 \le \mathrm{precisionBudget}$; `relativePatchComplexity oldPatch` $\le p$, where `relativePatchComplexity A` $= (D+E) + \log(1 + \mathrm{lip})$ with $\mathrm{lip}$ the Lipschitz constant of its kernel; $e^{-p} \le a$; and `RelativePatchAbsoluteRule s n₀ p a Λ d₀` holds (a proposition defined by OpenAI quantifying over prime moduli $N : \mathrm{Fin}\,n_0 \to \mathbb N$ and $[0,1]$-valued functions on the integer box whose support is free of $(s+2)$-term progressions and has mean at least $a$, and asserting `RelativePatchSliceConclusion` for each). Then, with $M$ as above, the structure `PreparedRelativeInitializerScalarInputs` holds for `oldPatch`, the coordinate counts $j \mapsto$ (number of coordinates of layer $j$ of `prep.pad (max m s)`), the variable count `preparedRelativeInitializerVariableCount prep s M`, and the scalars $p$, $p_{\mathrm{rel}}$, $\mathrm{precisionBudget}$, `allocatedUniformChartLog M`, $a$, $\Lambda$, $n_0$, $d_0$; this is a structure bundling fourteen scalar inequalities and the rule `RelativePatchAbsoluteRule s n₀ pRelative a Λ d₀`.
--
--   Lean: `OAI.Erdos3.preparedRelativeInitializer_scalarInputs` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean#L248

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {m s D nX : ℕ}

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

theorem preparedRelativeInitializer_scalarInputs
    {nX s D E m n₀ d₀ : ℕ}
    (oldPatch : PolynomialPatch (Fin nX) s (D + E))
    (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    {p pRelative precisionBudget a Λ : ℝ}
    (hp : 2 ≤ p) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D))
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hcomplexity : relativePatchComplexity oldPatch ≤ p)
    (ha : Real.exp (-p) ≤ a)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    let M := preparationCoordinateCap s D (s * D)
    PreparedRelativeInitializerScalarInputs oldPatch
      (fun j => Fintype.card (prep.pad (max m s) j).Coord)
      (preparedRelativeInitializerVariableCount prep s M)
      p pRelative precisionBudget (allocatedUniformChartLog (M : ℝ)) a Λ n₀ d₀ := by
  sorry

end Erdos3
end
end OAI
