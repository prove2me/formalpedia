-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_relativePatchFinPositivePower_of_prepared
-- name    : OAI.Erdos3.exists_relativePatchFinPositivePower_of_prepared
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:02:52.999415+00:00
-- url     : https://prove2.me/theorems/bee28cd1-e68c-4593-ba73-6a3a68ed2965
-- title:
--   A prepared relative patch power passage yields a positive-power rule
-- statement:
--   Let $s$, $n_0$ and `stage` be natural numbers and `discount` a real number. Assume that there exist natural numbers `requiredPower` and `precisionPower` such that for every natural number `preparationPower` $\ge2$ there is a natural number `passagePower` $\ge2$ with `PreparedRelativePatchPowerPassage s n₀ stage discount requiredPower precisionPower preparationPower passagePower`. Then there is a natural number `power` $\ge2$ with `RelativePatchFinPositivePowerRule s n₀ stage discount power`. Both are propositions of OpenAI's: `RelativePatchFinPositivePowerRule s n₀ stage discount power` says that for all reals $p\ge2$, $a,\Lambda$ with $e^{-p}\le a\le\Lambda\le1$ and every $d_0$ satisfying `RelativePatchAbsoluteRule s n₀ p a Λ d₀`, every dimension $0<n_X\le p$, every box $N\colon\mathrm{Fin}\,n_X\to\mathbb N$ with all $N_i\ge\exp((p+2)^{\mathrm{power}})$, every $f\colon\mathbb Z^{n_X}\to\mathbb R$ with values in $[0,1]$ on `integerBox N` whose support in the box is free of $(s+2)$-term progressions (`IntegerVectorAPFree`), and every `PolynomialPatch (Fin nX) s d` $A$ with $0<d$, `relativePatchComplexity A` $\le p$, `relativePatchDistinctWeights A` $\le$ `stage` $+1$ and $e^{-p}\le$ `relativePatchBoxScore N f a A`, the conclusion `RelativePatchSliceConclusion s N f ((1 - discount) ^ (stage + 2) * Λ) (d₀ + s * d) ((p + 2) ^ power)` holds; `PreparedRelativePatchPowerPassage` is a proposition of the same shape with further data (a lowest-layer model of an old patch, a prepared rank family and polynomial coordinates) and hypotheses.
--
--   Lean: `OAI.Erdos3.exists_relativePatchFinPositivePower_of_prepared` in `lean/OAI/Combinatorics/Progressions/Estimates/RelativePatchPositivePowerInduction.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RelativePatchPositivePowerInduction.lean#L772

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct Classical

namespace ResidueBoxSlice

end ResidueBoxSlice

namespace PolynomialPatch.LowestLayerModel

variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {s D E j R : ℕ} {A : PolynomialPatch X s (D + E)}

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

variable {K X : Type*} [Fintype K] [Fintype X] [DecidableEq K] [DecidableEq X]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct

namespace PolynomialPatch.LowestLayerModel

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators

variable {K X : Type*} [Fintype K]

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

open VectorPolynomial
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

theorem exists_relativePatchFinPositivePower_of_prepared
    {s n₀ stage : ℕ} {discount : ℝ}
    (hpassage : ∃ requiredPower precisionPower : ℕ,
      ∀ preparationPower : ℕ, 2 ≤ preparationPower →
        ∃ passagePower : ℕ, 2 ≤ passagePower ∧
          PreparedRelativePatchPowerPassage s n₀ stage discount
            requiredPower precisionPower preparationPower passagePower) :
    ∃ power : ℕ, 2 ≤ power ∧ RelativePatchFinPositivePowerRule s n₀ stage discount power := by
  sorry

end Erdos3
end
end OAI
