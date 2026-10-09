-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_mixedCoveredJet_normalized_complex_integral
-- name    : OAI.Erdos3.VectorPolynomial.mixedCoveredJet_normalized_complex_integral
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T07:42:31.785682+00:00
-- url     : https://prove2.me/theorems/e8c09b63-df24-4c9e-b5c8-f97aaf38a7a2
-- title:
--   Normalized chart density transports a weighted complex integral to the jet torus
-- statement:
--   Fix the section data: a natural number $m$; for $j \in \mathrm{Fin}\,m$ finite types $I_j, O_j, J_j, E_j$, a natural number $n_j$ and a real subspace $U_j \subseteq \mathbb R^{J_j}$, with $V_j = $ `euclideanSubspace (U j)` its Euclidean copy and $W_j = $ `latticeSection (standardEuclideanLattice (J j)) V_j` the lattice $\mathbb Z^{J_j} \cap V_j$; an orthonormal basis $o_j$ of $V_j$ indexed by $I_j$; a basis $b_j$ of $V_j^\perp$ indexed by $\mathrm{Fin}\,n_j$ whose $\mathbb Z$-span is `projectedIntegerLattice V_j` (the orthogonal projection of $\mathbb Z^{J_j}$ onto $V_j^\perp$), this equality being the hypothesis $hb$; a $\mathbb Z$-basis $bW_j$ of $W_j$ indexed by $E_j$; a positive natural number $d$; the assumption that each $W_j$ is a full lattice in $V_j$; for each $j$ an additively left-invariant probability measure $\nu_j$ on the torus $V_j / W_j$; and for each $j$ and $t \in O_j$ a measurable set $\Omega_{j,t} \subseteq \mathbb R^{J_j}$ contained in the box $\{x : |x_i| < 1/2 \ \forall i\}$ (`standardLatticeSmallBox`). Let the source space be `MixedCoveredJetSource I O E n d` $= \prod_j \bigl((I_j \to O_j \to \mathbb R) \times (\mathrm{Fin}\,n_j \to O_j \to \mathbb Z)\bigr) \times \prod_j (O_j \to E_j \to \mathbb Z/d)$, with the measure $\mathrm{raw} = $ `mixedCoveredJetRawReference d`, the product over $j$ of Lebesgue measure times counting measure, times the uniform probability measure on the $\mathbb Z/d$ part. Let $\mathrm{chart} = $ `mixedCoveredJetChart U o b hb bW d`, a map from the source to `EuclideanJetLayers U O` $= \prod_j \prod_{O_j} V_j/W_j$ defined by OpenAI, let $\mathrm{region} = $ `mixedCoveredJetRegion U o b d Ω`, a subset of the source defined by OpenAI from $\Omega$, and let $\mathrm{haar} = \prod_j \prod_{O_j} \nu_j$. Let $\kappa = $ `coveredJetArrayScale U` $= \prod_j \mathrm{covol}(W_j)^{-|O_j|}$. For every measurable $f : \text{source} \to \mathbb R$ with $f \ge 0$ and $f = 0$ off $\mathrm{region}$, and every measurable $\varphi : $ `EuclideanJetLayers U O` $\to \mathbb C$,
--   $$\int f(z)\,\varphi(\mathrm{chart}\,z)\,d\mathrm{raw}(z) = \int g(y)\,\varphi(y)\,d\mathrm{haar}(y),$$
--   where $g = $ `restrictedChartDensity chart region 1 (f / κ)`; by definition $g(y) = f(x)/\kappa$ for a point $x \in \mathrm{region}$ with $\mathrm{chart}\,x = y$ (chosen by `Function.extend`) when one exists, and $g(y) = 0$ otherwise.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.mixedCoveredJet_normalized_complex_integral` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredSiteExpansion.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B128` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredSiteExpansion.lean#L144

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B128

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω

include hΩ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d

include hΩm hΩ in
theorem mixedCoveredJet_normalized_complex_integral
    (f : MixedCoveredJetSource I O E n d → ℝ) (hfm : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) (hfs : ∀ z ∉ region, f z = 0)
    (φ : EuclideanJetLayers U O → ℂ) (hφ : Measurable φ) :
    (∫ z, (f z : ℂ) * φ (chart z) ∂raw) =
      ∫ y, (restrictedChartDensity chart region 1
        (fun z => f z / coveredJetArrayScale (O := O) U) y : ℂ) * φ y ∂haar := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
