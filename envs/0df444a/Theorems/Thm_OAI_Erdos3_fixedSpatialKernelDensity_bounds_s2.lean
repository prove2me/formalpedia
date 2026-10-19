-- Prove2me | Theorems.Thm_OAI_Erdos3_fixedSpatialKernelDensity_bounds_s2
-- name    : OAI.Erdos3.fixedSpatialKernelDensity_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:30:33.424983+00:00
-- url     : https://prove2.me/theorems/d5eaca63-6cab-4e39-81c0-78b87aa2fcdc
-- title:
--   The fixed spatial kernel density is bounded by the block density cap and Lipschitz with the block Lipschitz constant
-- statement:
--   Let $G$, $X$, $T$ be types with $X$ finite with decidable equality and $T$ finite, let $e : G \simeq X \sqcup (X \sqcup T)$ be an equivalence, let $W, L$ be reals and $z : \texttt{Option}\ G \times X \to \mathbb{R}$. For $b \in \{\mathrm{false}, \mathrm{true}\}$ let $M_b$ = `fixedSpatialKernelBlock e W L z b`, the $X \times X$ real matrix with entries $M_b(x, i) = \frac{L}{1 + W}\, z(\mathrm{some}(e^{-1}(\iota_b(i))), x)$, where $\iota_{\mathrm{false}}(i)$ is $i$ in the first copy of $X$ and $\iota_{\mathrm{true}}(i)$ is $i$ in the second copy. Assume $\det M_{\mathrm{false}} \ne 0$ and $\det M_{\mathrm{true}} \ne 0$, and let $E_b$ = `fixedSpatialKernelBlockEquiv e W L z b` be the corresponding continuous linear automorphism of $\mathbb{R}^X$ (defined by OpenAI).
--
--   Let $\rho$ = `fixedSpatialKernelDensity e W L z h0 h1`, a real function on $\mathbb{R}^X$ defined by OpenAI (the density of the fixed spatial kernel block image, `fixedSpatialBlockDensity` built from $z(\mathrm{none}, \cdot)$, the remaining columns indexed by $T$ averaged over the unit box, and $E_{\mathrm{false}}$, $E_{\mathrm{true}}$). Then:
--   1. for every $x \in \mathbb{R}^X$, $0 \le \rho(x) \le$ `fixedSpatialBlockDensityCap` $(E_{\mathrm{true}})$;
--   2. $\rho$ is Lipschitz with constant `fixedSpatialBlockDensityLipschitz` $(E_{\mathrm{false}}, E_{\mathrm{true}})$.
--
--   Here `fixedSpatialBlockDensityCap` and `fixedSpatialBlockDensityLipschitz` are explicit nonnegative constants defined by OpenAI in terms of the given linear automorphisms.
--
--   Lean: `OAI.Erdos3.fixedSpatialKernelDensity_bounds_s2`, which states OpenAI's `OAI.Erdos3.fixedSpatialKernelDensity_bounds` (in `lean/OAI/Combinatorics/Progressions/Linear/FixedSpatialKernelSliceDensity.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B074`, `OAIE3v2B082` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/FixedSpatialKernelSliceDensity.lean (declaration OAI.Erdos3.fixedSpatialKernelDensity_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B082

section

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)

variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

omit [Fintype G] in
theorem fixedSpatialKernelDensity_bounds_s2 :
    (∀ x, fixedSpatialKernelDensity e W L z h0 h1 x ∈ Set.Icc (0 : ℝ)
      (fixedSpatialBlockDensityCap (fixedSpatialKernelBlockEquiv e W L z true h1))) ∧
      LipschitzWith (fixedSpatialBlockDensityLipschitz
        (fixedSpatialKernelBlockEquiv e W L z false h0)
        (fixedSpatialKernelBlockEquiv e W L z true h1))
        (fixedSpatialKernelDensity e W L z h0 h1) := by
  sorry

end Erdos3

end

end OAI
end
