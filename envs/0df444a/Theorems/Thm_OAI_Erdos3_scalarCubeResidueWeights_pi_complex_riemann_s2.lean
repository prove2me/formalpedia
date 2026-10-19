-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarCubeResidueWeights_pi_complex_riemann_s2
-- name    : OAI.Erdos3.scalarCubeResidueWeights_pi_complex_riemann_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:31:52.550764+00:00
-- url     : https://prove2.me/theorems/fe724112-993c-439b-8d64-68a2ed2f4844
-- title:
--   Riemann-sum error for a Lipschitz bounded function under products of residue-conditioned scalar-cube weights
-- statement:
--   All named objects below are defined by OpenAI.
--
--   Let $G$ and $I$ be finite types with decidable equality. Let $L, M : G \to \mathbb{N}$ with $L_g > 0$, and for each $g \in G$ and $i \in \mathrm{Option}\ I$ let $m_{g,i}$ be a natural number with $0 < m_{g,i} \le M_g$ and $r_{g,i} \in \mathbb{Z}/m_{g,i}\mathbb{Z}$. Assume, for every $g$, $(|I| + 1)\,M_g \le L_g$ and
--   $$\texttt{scalarCubeGridBoundaryConstant}\ I\cdot \frac{M_g}{L_g} < \operatorname{vol}(\texttt{scalarCubeDomain}\ I),$$
--   where `scalarCubeGridBoundaryConstant I` $= |\mathrm{Bool}\times\mathrm{Finset}\ I|\cdot 4^{|I|}\cdot 2\cdot(|I|+1)$ and `scalarCubeDomain I` is the open set of $a \in \mathbb{R}^{\mathrm{Option}\ I}$ with $a_{\mathrm{none}} + \sum_{i \in t} a_{\mathrm{some}\ i} \in (0,1)$ for every finite $t \subseteq I$ (vol is Lebesgue measure, as a real number).
--
--   For each $g$ let $w_g$ = `scalarCubeResidueWeights I (L g) (M g) … (m g) (r g) …`, the uniform probability weights on the integer points $z$ of OpenAI's scalar cube box `IntegerScalarCubeBox I (L g)` that satisfy $z_i \equiv r_{g,i} \pmod{m_{g,i}}$ for all $i$ (the integer scalar cube weights conditioned on this residue set), and let $w = \prod_g w_g$ be the product weights. Let $\varphi : \mathbb{R}^{G \times \mathrm{Option}\ I} \to \mathbb{C}$ be $K$-Lipschitz ($K \in \mathbb{R}_{\ge 0}$) and bounded by $B \ge 0$ in norm. Then
--   $$\Bigl\| \mathbb{E}_{z \sim w}\, \varphi\Bigl(\bigl(\tfrac{z_{g,i}}{L_g}\bigr)_{g,i}\Bigr) - \int \varphi\, d\,\texttt{scalarCubeProductMeasure}\ G\ I \Bigr\| \le 2\Bigl(\frac{2B\cdot\texttt{scalarCubeGridBoundaryConstant}\ I}{\operatorname{vol}(\texttt{scalarCubeDomain}\ I)} + K\Bigr)\sum_{g \in G}\frac{M_g}{L_g},$$
--   where `scalarCubeProductMeasure G I` is the product over $g \in G$ of the normalized Lebesgue (uniform probability) measure on `scalarCubeDomain I`.
--
--   Lean: `OAI.Erdos3.scalarCubeResidueWeights_pi_complex_riemann_s2`, which states OpenAI's `OAI.Erdos3.scalarCubeResidueWeights_pi_complex_riemann` (in `lean/OAI/Combinatorics/Progressions/Lattices/OriginalKernelResidueRetained.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B061`, `OAIE3v2B093` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/OriginalKernelResidueRetained.lean (declaration OAI.Erdos3.scalarCubeResidueWeights_pi_complex_riemann)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B061
import Definitions.Def_OAIE3v2B093

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem scalarCubeResidueWeights_pi_complex_riemann_s2 {G I : Type*}
    [Fintype G] [DecidableEq G] [Fintype I] [DecidableEq I]
    (L M : G → ℕ) (hL : ∀ g, 0 < L g) (m : G → Option I → ℕ)
    (r : ∀ g i, ZMod (m g i)) (hm : ∀ g i, 0 < m g i)
    (hmM : ∀ g i, m g i ≤ M g)
    (hsize : ∀ g, (Fintype.card I + 1) * M g ≤ L g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant I * ((M g : ℝ) / L g) <
      volume.real (scalarCubeDomain I))
    (φ : (G → Option I → ℝ) → ℂ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    ‖(FiniteProbabilityWeights.pi (fun g => scalarCubeResidueWeights I (L g) (M g) (hL g)
      (m g) (r g) (hm g) (hmM g) (hsize g))).complexMean
        (fun z => φ (fun g i => (z g i : ℝ) / L g)) -
      ∫ x, φ x ∂scalarCubeProductMeasure G I‖ ≤
      2 * (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) *
        ∑ g, (M g : ℝ) / L g := by
  sorry

end Erdos3

end

end OAI
end
