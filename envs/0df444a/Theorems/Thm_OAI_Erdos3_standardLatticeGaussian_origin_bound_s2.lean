-- Prove2me | Theorems.Thm_OAI_Erdos3_standardLatticeGaussian_origin_bound_s2
-- name    : OAI.Erdos3.standardLatticeGaussian_origin_bound_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:45.713577+00:00
-- url     : https://prove2.me/theorems/cca7497a-e715-41ac-aa64-06438ce0dce5
-- title:
--   The normalized Gaussian mass of the standard lattice at the origin is at most (1 + 2t)^n
-- statement:
--   Let $\iota$ be a finite type, $n = |\iota|$, and let $\mathbb{Z}^\iota \subseteq \mathbb{R}^\iota$ be the standard lattice in Euclidean space (`standardEuclideanLattice ι`, the $\mathbb{Z}$-span of the standard basis). Let $t > 0$. Then
--   $$\texttt{normalizedLatticeGaussian}\ \mathbb{Z}^\iota\ t\ 0 \le (1 + 2t)^{n},$$
--   where `normalizedLatticeGaussian Λ t x` $= (\sqrt t)^{\dim} \operatorname{covol}(\Lambda) \sum_{m \in \Lambda} \exp(-\pi t \|x - m\|^2)$ (defined by OpenAI), with $\dim = n$ here.
--
--   Lean: `OAI.Erdos3.standardLatticeGaussian_origin_bound_s2`, which states OpenAI's `OAI.Erdos3.standardLatticeGaussian_origin_bound` (in `lean/OAI/Combinatorics/Progressions/Lattices/StandardLatticeGaussianBound.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B067` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/StandardLatticeGaussianBound.lean (declaration OAI.Erdos3.standardLatticeGaussian_origin_bound)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B067

section

namespace OAI

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

theorem standardLatticeGaussian_origin_bound_s2 {t : ℝ} (ht : 0 < t) :
    normalizedLatticeGaussian (standardEuclideanLattice ι) t 0 ≤ (1 + 2 * t) ^ Fintype.card ι := by
  sorry

end Erdos3

end

end OAI
end
