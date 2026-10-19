-- Prove2me | Theorems.Thm_OAI_Erdos3_canonicalSlicedPrincipalDensity_law_bounds_s2
-- name    : OAI.Erdos3.canonicalSlicedPrincipalDensity_law_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:47.273259+00:00
-- url     : https://prove2.me/theorems/51cce465-e19a-48cb-b3f7-60e160055108
-- title:
--   The law of a principal slice value on the unit box has the canonical sliced density, which is bounded, Lipschitz and a probability density
-- statement:
--   Let $B$ and $F$ be finite types with decidable equality, with $|B| \ge 4$, and fix $i \in F$. Let $c : B \to \mathbb{R}$ and $\mathrm{lower}, \mathrm{width} : B \times F \to \mathbb{R}$, and let $a, \delta$ be reals with $a > 0$, $\delta > 0$, $a \le |c_b|$ for all $b \in B$, $\delta \le \mathrm{width}(p)$ and $0 \le \mathrm{lower}(p)$ for all $p \in B \times F$.
--
--   Let $f : \mathbb{R} \to \mathbb{R}$ be `canonicalSlicedPrincipalDensity hB i c lower width`, a function defined by OpenAI (via a fixed decomposition of $B$ into four blocks and the identification of $F$ with $\mathrm{Option}\{j \in F : j \ne i\}$). Let $d = |\{j \in F : j \ne i\}| = |F| - 1$ and
--   $$K = \texttt{SlicedProductBlock.uniformCap}\ \{j \ne i\}\ (a\,\delta^{d+1}) = (a\,\delta^{d+1})^{-1}\cdot 4^{d}.$$
--   Let $\Sigma : \mathbb{R}^{B \times F} \to \mathbb{R}$ be `principalSliceValue c lower width`, i.e.
--   $$\Sigma(x) = \sum_{b \in B} c_b \prod_{k \in F} \bigl(\mathrm{lower}(b,k) + \mathrm{width}(b,k)\, x(b,k)\bigr).$$
--   Then:
--   1. the push-forward under $\Sigma$ of `unitBoxMeasure (B × F)` (Lebesgue measure restricted to the box $(0,1]^{B \times F}$) equals the measure with density $\max(f, 0)$ with respect to Lebesgue measure on $\mathbb{R}$ (`realDensityMeasure volume f`);
--   2. $f(x) \in [0, K]$ for all $x \in \mathbb{R}$;
--   3. $f$ is Lipschitz with constant $K \cdot 2K$;
--   4. $f$ is integrable and $\int_{\mathbb{R}} f(x)\,dx = 1$.
--
--   Lean: `OAI.Erdos3.canonicalSlicedPrincipalDensity_law_bounds_s2`, which states OpenAI's `OAI.Erdos3.canonicalSlicedPrincipalDensity_law_bounds` (in `lean/OAI/Combinatorics/Progressions/Probability/SlicedRemainderDensityFamily.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B030`, `OAIE3v2B048` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/SlicedRemainderDensityFamily.lean (declaration OAI.Erdos3.canonicalSlicedPrincipalDensity_law_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B030
import Definitions.Def_OAIE3v2B048

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem canonicalSlicedPrincipalDensity_law_bounds_s2
    {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ) (lower width : B × F → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ b, a ≤ |c b|) (hw : ∀ p, δ ≤ width p) (hl : ∀ p, 0 ≤ lower p) :
    let f := canonicalSlicedPrincipalDensity hB i c lower width
    let K := SlicedProductBlock.uniformCap {j : F // j ≠ i}
      (a * δ ^ (Fintype.card {j : F // j ≠ i} + 1)) (mul_pos ha (pow_pos hδ _))
    (unitBoxMeasure (B × F)).map (principalSliceValue c lower width) = realDensityMeasure volume f ∧
      (∀ x, f x ∈ Set.Icc (0 : ℝ) K) ∧ LipschitzWith (K * (2 * K)) f ∧
        Integrable f ∧ (∫ x, f x) = 1 := by
  sorry

end Erdos3

end

end OAI
end
