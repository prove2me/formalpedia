-- Prove2me | Theorems.Thm_OAI_Erdos3_affineReferenceInput_mask_and_depth
-- name    : OAI.Erdos3.affineReferenceInput_mask_and_depth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:16:38.638973+00:00
-- url     : https://prove2.me/theorems/3025ee74-83e2-44f3-a290-ded2959b2a9b
-- title:
--   The affine reference input bounds the sampler prime mask, the comparison depth and T + 4
-- statement:
--   Let $\iota$ be a finite type, $\mathrm{prime} : \iota \to \mathbb{N}$ an injective function with every $\mathrm{prime}(i)$ prime, and $D$ a positive natural number. Let $\varepsilon, L, T, C, U$ be real numbers with $0 < \varepsilon \le 1$, $0 \le U$, $0 \le L$, $0 \le T$, $0 \le C$, $L \le U$, $T \le U$, $C \le U$, $\varepsilon^{-1} \le e^{U}$ and $D \le e^{U}$. Write $\Lambda = $ `affineReferenceInput ε U`, an explicit real-valued function of OpenAI. Then:
--
--   - the number of elements of the finite set `affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D` is at most $\Lambda$ (this set of indices is OpenAI's union of `affineInitialPrimeMask prime (ε/(2+ε)) (affineComparisonScale ε L T C) 1 1` and `periodPrimeCoordinates prime D`, and `affineComparisonScale` is OpenAI's real-valued scale);
--   - $\texttt{affineRemovalDepth}\ T + \texttt{affineComparisonTail}\ \varepsilon\ L\ T \le \Lambda$, these being natural numbers defined by OpenAI;
--   - $T + 4 \le \Lambda$.
--
--   Lean: `OAI.Erdos3.affineReferenceInput_mask_and_depth` in `lean/OAI/Combinatorics/Progressions/Lattices/PrimeCoordinateCells.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/PrimeCoordinateCells.lean#L489

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

theorem affineReferenceInput_mask_and_depth {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (D : ℕ) (hD : 0 < D) {epsilon L T C U : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hU : 0 ≤ U)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hLU : L ≤ U) (hTU : T ≤ U) (hCU : C ≤ U)
    (hepsInv : epsilon⁻¹ ≤ Real.exp U) (hDU : (D : ℝ) ≤ Real.exp U) :
    ((affineSamplerPrimeMask prime (epsilon / (2 + epsilon))
      (affineComparisonScale epsilon L T C) 1 1 D).card : ℝ) ≤ affineReferenceInput epsilon U ∧
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affineReferenceInput epsilon U ∧
    T + 4 ≤ affineReferenceInput epsilon U := by
  sorry

end Erdos3
end
end OAI
