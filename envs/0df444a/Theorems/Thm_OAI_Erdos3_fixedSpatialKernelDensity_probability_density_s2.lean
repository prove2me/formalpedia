-- Prove2me | Theorems.Thm_OAI_Erdos3_fixedSpatialKernelDensity_probability_density_s2
-- name    : OAI.Erdos3.fixedSpatialKernelDensity_probability_density_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:32.389184+00:00
-- url     : https://prove2.me/theorems/12c03a38-a219-4d3f-9343-24d85fab1bdd
-- title:
--   The fixed spatial kernel density is a nonnegative integrable function with total integral 1
-- statement:
--   Let $G$ be a type, $X$ a finite type with decidable equality, $T$ a finite type, and $e : G \simeq X \sqcup (X \sqcup T)$ an equivalence. Let $W, L$ be reals and $z : \mathrm{Option}\ G \times X \to \mathbb{R}$. For a Boolean $b$, let $M_b$ = `fixedSpatialKernelBlock e W L z b`, the $X \times X$ real matrix defined by OpenAI with entries
--   $$(M_b)_{x,i} = \frac{L}{1 + W}\, z\bigl(\mathrm{some}(e^{-1}(\iota_b(i))),\ x\bigr),$$
--   where $\iota_{\mathrm{false}}(i)$ is $i$ in the first copy of $X$ and $\iota_{\mathrm{true}}(i)$ is $i$ in the second copy. Assume $\det M_{\mathrm{false}} \ne 0$ and $\det M_{\mathrm{true}} \ne 0$.
--
--   Let $f : \mathbb{R}^X \to \mathbb{R}$ be `fixedSpatialKernelDensity e W L z h0 h1`, a function defined by OpenAI (the density of the block law built from the unit box measure on $\mathbb{R}^T$, the offset $x \mapsto z(\mathrm{none}, x)$, the remaining term `fixedSpatialKernelRest e W L z`, and the two invertible blocks $M_{\mathrm{false}}$, $M_{\mathrm{true}}$). Then $f(x) \ge 0$ for every $x \in \mathbb{R}^X$, $f$ is integrable with respect to Lebesgue measure, and $\int_{\mathbb{R}^X} f(x)\,dx = 1$.
--
--   Lean: `OAI.Erdos3.fixedSpatialKernelDensity_probability_density_s2`, which states OpenAI's `OAI.Erdos3.fixedSpatialKernelDensity_probability_density` (in `lean/OAI/Combinatorics/Progressions/Linear/FixedSpatialKernelSliceDensity.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B074` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/FixedSpatialKernelSliceDensity.lean (declaration OAI.Erdos3.fixedSpatialKernelDensity_probability_density)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B074

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
theorem fixedSpatialKernelDensity_probability_density_s2 :
    (∀ x, 0 ≤ fixedSpatialKernelDensity e W L z h0 h1 x) ∧
      Integrable (fixedSpatialKernelDensity e W L z h0 h1) ∧
      (∫ x, fixedSpatialKernelDensity e W L z h0 h1 x) = 1 := by
  sorry

end Erdos3

end

end OAI
end
