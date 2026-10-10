-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProgressionCoveredExpectation_density
-- name    : OAI.Erdos3.VectorPolynomial.allocatedProgressionCoveredExpectation_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:45:46.833991+00:00
-- url     : https://prove2.me/theorems/aa604f00-3a3c-4b5f-b960-a717ca1cf9c5
-- title:
--   The covered progression expectation as an integral against mixed jet densities
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality, $O_j$ finite types, `rows` $j\colon O_j\to$ `Finset α`, $x\colon G\to$ `IntegerScalarCubeBox α S.value`, $Q_j$ finite types, `hb` the hypothesis that the $\mathbb Z$-span of the range of `basis j` is `projectedIntegerLattice (euclideanSubspace (U j))` for every $j$, $o_j$ an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$, $b^W_j$ a $\mathbb Z$-basis indexed by $Q_j$ of the lattice `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, and $d\ne0$ a natural number. Write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`; let $H_0,\mathrm{step}_0\colon\mathcal T\to\mathbb N$ with $H_0(t)>0$ (`hH₀`), $c_0\colon\mathcal T\to\mathbb Z$ with `integerProgressionSupport (c₀ t) (step₀ t) (H₀ t)` $\subseteq[0,\ $`allocatedPrincipalSides B U basis S t`$)$ (`hsubset₀`), $q\in\mathbb N$ (`modulus`), $r_0\colon\mathcal T\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, and assume (`hcell`) that the event `principalResidueLabel q y = r₀` has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀`; let `wholeLaw` be `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ … hH₀ hsubset₀ q r₀ hcell`, a `FiniteProbabilityWeights` on tuples $y$. Let the coefficient torus $\mathbb T=$ `CoefficientTorus U` (over the variables `LayerSamplerVariables G I n B`) be compact with a Borel measurable structure, $\mu$ a measure on $\mathbb T$, and $\nu_j$ a measure on the quotient of `euclideanSubspace (U j)` by that lattice section, for each $j$; let $\xi=\prod_j\prod_{O_j}\nu_j$ on `EuclideanJetLayers U O`. Write `density` $=$ `allocatedCoefficientDensity B U basis hb o hR hσ S` (a real function on $\mathbb T$), `cover` $=$ multiplication by $d$ on $\mathbb T$ (`quotientIntegerCover`), and `source` $=$ `allocatedCoefficientSource B U basis hR hσ S` (a product measure on coefficient arrays). Assume `CoefficientDeckDensityLaw U bW basis hb o μ source density d` (`hdeck`: the image of `source` $\otimes$ uniform(`CoefficientDeckResidues Q d`) under `canonicalCoefficientDeckSample` is the measure with density `density ∘ cover` with respect to $\mu$). Let $g$ assign to each tuple $y\in$ `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S)` a measurable function $g_y\ge0$ on `EuclideanJetLayers U O`, integrable for $\xi$, such that the image of the measure with density `density ∘ cover` w.r.t. $\mu$ under `euclideanCoefficientJetMap U (root y) (dirs y) rows` equals the measure with density $g_y$ w.r.t. $\xi$, where root $y=$ `allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y` and dirs $y=$ `allocatedPhysicalCubeDirections B U basis S x y`. Let $\varphi\colon$ `EuclideanJetLayers U O` $\to\mathbb C$ be measurable with $\|\varphi\|\le1$. Then
--   $$\texttt{allocatedProgressionCoveredExpectation}\ \ldots\ (p\mapsto\varphi(p.2))\ \ldots=\int\Big(\sum_y\mathrm{wholeLaw}(y)\,g_y(z)\Big)\,\varphi(z)\,d\xi(z),$$
--   where `allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d F H₀ step₀ c₀ hH₀ hsubset₀ q r₀ hcell` is the complex number $\int\sum_y\mathrm{wholeLaw}(y)\,F\big(\text{frozen part of }c,\ \texttt{euclideanCoefficientJetMap}\ U\ (\mathrm{root}\ y)\ (\mathrm{dirs}\ y)\ \mathrm{rows}\ (\texttt{canonicalCoefficientDeckSample}\ \ldots\ c\ e)\big)\,d(\mathrm{source}\otimes\mathrm{uniform})(c,e)$, the frozen part being the first component of `allocatedCoefficientSplit B U basis S c`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedProgressionCoveredExpectation_density` in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedProgressionDensityIdentity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B136` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedProgressionDensityIdentity.lean#L326

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B136

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => (∫ p, FiniteProbabilityWeights.complexMean wholeLaw (fun y =>
  F (Prod.fst ((allocatedCoefficientSplit B U basis S) (Prod.fst p)),
    euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
      (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
  ∂(Measure.prod source (PMF.toMeasure deck)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] [∀ j, (ν j).IsAddLeftInvariant]
  [∀ j, IsProbabilityMeasure (ν j)] [DecidableEq G]
  [∀ index, DecidableEq (O index)] in
theorem allocatedProgressionCoveredExpectation_density
    (hdeck : CoefficientDeckDensityLaw U bW basis hb o μ source density d)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U O → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) ξ)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
      (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure ξ (g y))
    (φ : EuclideanJetLayers U O → ℂ) (hφ : Measurable φ) (hbφ : ∀ z, ‖φ z‖ ≤ 1) :
    allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d
      (fun p => φ p.2) H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell =
      ∫ z, ((wholeLaw).mean (fun y => g y z) : ℂ) * φ z ∂ξ := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
