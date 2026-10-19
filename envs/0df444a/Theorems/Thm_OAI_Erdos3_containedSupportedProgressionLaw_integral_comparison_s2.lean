-- Prove2me | Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_integral_comparison_s2
-- name    : OAI.Erdos3.containedSupportedProgressionLaw_integral_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:32:44.069993+00:00
-- url     : https://prove2.me/theorems/9265bfb4-614a-4017-91dd-0a7cb1c5e4ab
-- title:
--   Splitting the contained supported progression law into two groups of axes transfers a pointwise integral comparison to the whole law
-- statement:
--   Let $\mathcal{D}$ and $\alpha$ be finite types with decidable equality, let $B$ assign to each $d \in \mathcal{D}$ a finite type $B_d$ with decidable equality, and let $h : \mathcal{D} \to \mathbb{N}$. The index set `PrincipalTupleIndex B h` consists of the triples $j = (d, b, t)$ with $d \in \mathcal{D}$, $b \in B_d$ and $t < h_d$; for $j = (d, b, t)$ write $d(j) = d$. Let $L, H, \mathrm{step}$ be natural-number functions and $c$ an integer function on this index set, with $L_j > 0$ and $H_j > 0$ for all $j$, and assume that for every $j$ the progression $\{c_j + \mathrm{step}_j \cdot n : 0 \le n < H_j\}$ (OpenAI's `integerProgressionSupport (c j) (step j) (H j)`) is contained in $\{0, 1, \dots, L_j - 1\}$. Let $q$ be a natural number and $r$ a function assigning to each index $j$ and each element of $\mathrm{Option}\,\alpha$ a residue in $\mathbb{Z}/q\mathbb{Z}$. A principal integer tuple with lengths $L$ (an element of OpenAI's `PrincipalIntegerTuples B h α L`) assigns to each index $j$ a point $y_j$ of the integer cube $\mathrm{Option}\,\alpha \to [-L_j, L_j) \cap \mathbb{Z}$. Assume that the residue cell $\{y : y_j(i) \equiv r_j(i) \pmod q \text{ for all } j, i\}$ has positive mass under `principalTupleWeights B h H hH`, the product over $j$ of OpenAI's integer scalar cube weights with lengths $H_j$ (the uniform distribution on OpenAI's integer scalar cube set inside the cube $[-H_j, H_j)^{\mathrm{Option}\,\alpha}$). Let $P$ be a decidable predicate on $\mathcal{D}$.
--
--   We use the following probability laws defined by OpenAI (with all the data above as arguments).
--   - `containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell` is a probability law on principal integer tuples with lengths $L$: the image of the principal tuple weights with lengths $H$, conditioned on the residue cell given by $r$, under OpenAI's map `containedProgressionTupleMap`, which sends a cube point $z$ at index $j$ to the point with coordinates $c_j + \mathrm{step}_j\, z(\mathrm{none})$ at none and $\mathrm{step}_j\, z(i)$ at the other coordinates (when $z$ lies in the integer scalar cube set; otherwise to $0$).
--   - For a predicate $Q$ on $\mathcal{D}$, `containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell Q` is the analogous law on the tuples indexed only by the $j$ with $Q(d(j))$ (OpenAI's `PrincipalAxisTuples Q L`), built from the product over those $j$ of the coordinatewise conditioned cube weights.
--   - For $u$ indexed by the $j$ with $P(d(j))$ and $v$ indexed by the $j$ with $\neg P(d(j))$, `principalAxisJoin P u v` is the full tuple equal to $u_j$ when $P(d(j))$ and to $v_j$ otherwise.
--
--   Write $\lambda$ for the contained supported progression law, $\lambda_P$ for the axis law with predicate $P$ and $\lambda_{\neg P}$ for the axis law with predicate $\neg P$. Let $(\Omega, \mu)$ be a measurable space with a measure, let $f : \Omega \to (\text{principal integer tuples with lengths } L) \to \mathbb{C}$ be such that $p \mapsto f(p, y)$ is $\mu$-integrable for every $y$, let $g$ be a complex-valued function on the tuples indexed by the $j$ with $P(d(j))$, and let $E$ be a real number. Assume that for every $u$ with $\lambda_P(u) \ne 0$,
--   $$\Bigl|\int_\Omega \mathbb{E}_{v \sim \lambda_{\neg P}}\, f\bigl(p, \texttt{principalAxisJoin}\ P\ u\ v\bigr)\, d\mu(p) - g(u)\Bigr| \le E.$$
--   Then
--   $$\Bigl|\int_\Omega \mathbb{E}_{y \sim \lambda}\, f(p, y)\, d\mu(p) - \mathbb{E}_{u \sim \lambda_P}\, g(u)\Bigr| \le E.$$
--   (Expectations are the complex means `complexMean` of OpenAI's finite probability weights; the integrals are Bochner integrals.)
--
--   Lean: `OAI.Erdos3.containedSupportedProgressionLaw_integral_comparison_s2`, which states OpenAI's `OAI.Erdos3.containedSupportedProgressionLaw_integral_comparison` (in `lean/OAI/Combinatorics/Progressions/Geometry/PrincipalCubeSupportedCell.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/PrincipalCubeSupportedCell.lean (declaration OAI.Erdos3.containedSupportedProgressionLaw_integral_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

theorem containedSupportedProgressionLaw_integral_comparison_s2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → PrincipalIntegerTuples B h α L → ℂ) (hf : ∀ y, Integrable (fun p => f p y) μ)
    (g : PrincipalAxisTuples (α := α) P L → ℂ) {E : ℝ}
    (hpoint : ∀ u,
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0 →
      ‖(∫ p, (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
        (fun v => f p (principalAxisJoin P u v)) ∂μ) - g u‖ ≤ E) :
    ‖(∫ p, (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean (f p) ∂μ) -
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean g‖ ≤ E := by
  sorry

end Erdos3

end

end OAI
end
