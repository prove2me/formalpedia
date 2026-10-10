-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoveredProfile_test_integral
-- name    : OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_test_integral
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:08:06.387727+00:00
-- url     : https://prove2.me/theorems/b6f2f03e-8e2c-4b2d-babd-87b498fb2ee0
-- title:
--   Covered fixed-test integral equals a torus integral of the covered profile density
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$ with real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, $W_j = \mathbb Z^{J_j} \cap V_j$ (`latticeSection`), and bases $b_j$ of $V_j^\perp$ indexed by $\mathrm{Fin}\,n_j$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$ (hypotheses $hR$, $h\sigma$); a layer-sampler scale `S : LayerSamplerScale B U b R σ`; a type $\alpha$ with decidable equality and a point $x : G \to $ `IntegerScalarCubeBox α S.value`; a grid tuple $u$ in `PrincipalAxisTuples (allocatedGridAxis U b S.value) (allocatedPrincipalSides B U b S)` and a non-grid tuple $v_0$ in `PrincipalAxisTuples (¬ allocatedGridAxis U b S.value) (allocatedPrincipalSides B U b S)`; finite types $O_j$ and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$; finite types $Q_j$; the hypothesis $hb$ that the $\mathbb Z$-span of each $b_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $W_j$ indexed by $Q_j$; a positive natural number $d$; the assumption that each $W_j$ is a full lattice in $V_j$; additively left-invariant probability measures $\nu_j$ on the tori $V_j/W_j$; and for each $j$ and $t \in O_j$ a measurable set $\Omega_{j,t} \subseteq \mathbb R^{J_j}$ contained in the box $\{x : |x_i| < 1/2\}$ (`standardLatticeSmallBox`).
--
--   Let $f$ be a measurable, nonnegative real function on `AllocatedLongJetRows B U b S O`, integrable with respect to `allocatedLongJetReference B U b S O`, such that `allocatedGridlessWeightedKernel B U b S x u v₀ rows d fg f z` $= 0$ for every $z$ outside `mixedCoveredJetRegion U o b d Ω`, where `fg` $=$ `allocatedGridJetDensity B U b hR hσ S x u v₀ rows` (both defined by OpenAI). Let $F : $ `EuclideanJetLayers U O` $\to \mathbb C$ be measurable with $\|F(z)\| \le C$ for all $z$. Then
--   $$\int\!\!\int f(z)\cdot\texttt{allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d}\,(p \mapsto F(p_2))\,(a, z) = \int g(y)\,F(y)\,d\Bigl(\prod_j \prod_{O_j} \nu_j\Bigr)(y),$$
--   where the inner integral is in $z$ against `allocatedLongJetReference B U b S O`, the outer in $a$ against `allocatedFrozenCoefficientSource B U b hR hσ S`, and $g = $ `allocatedCoveredProfileDensity B U b hR hσ S x u v₀ rows hb o bW d Ω f`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_test_integral` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedRowIdealSupport.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B140`, `OAIErdos3B169`, `OAIErdos3B170` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedRowIdealSupport.lean#L268

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B140
import Definitions.Def_OAIErdos3B169
import Definitions.Def_OAIErdos3B170

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

local notation "Output" => (Σ _e : OneCubeActiveRow grid, Unit)

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "rawRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v rows

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "mixedRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v₀ rows
local notation "fd" => coefficientDeckJetDensity (B := Q) root dirs rows d
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

omit [Fintype α] in
include hΩm hΩ in
theorem allocatedCoveredProfile_test_integral
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f)
    (hf : Integrable f longRef) (hf0 : ∀ z, 0 ≤ f z)
    (hfs : ∀ z ∉ mixedCoveredJetRegion (E := Q) U o b d Ω,
      allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z = 0)
    (F : EuclideanJetLayers U O → ℂ) (hF : Measurable F)
    {C : ℝ} (hbound : ∀ z, ‖F z‖ ≤ C) :
    (∫ a, ∫ z, (f z : ℂ) *
      allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d (fun p => F p.2) a z
      ∂longRef ∂allocatedFrozenCoefficientSource B U b hR hσ S) =
    ∫ y, (allocatedCoveredProfileDensity B U b hR hσ S x u v₀ rows hb o bW d Ω f y : ℂ) *
      F y ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
