-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoveredProfile_test_integral_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_test_integral_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:20:31.980997+00:00
-- url     : https://prove2.me/theorems/9c4377a6-57cd-46f8-a0c4-8491a13f61cf
-- title:
--   Covered fixed-test integral equals a torus integral of the covered profile density
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$ with real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, $W_j = \mathbb Z^{J_j} \cap V_j$ (`latticeSection`), and bases $b_j$ of $V_j^\perp$ indexed by $\mathrm{Fin}\,n_j$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$ (hypotheses $hR$, $h\sigma$); a layer-sampler scale `S : LayerSamplerScale B U b R σ`; a type $\alpha$ with decidable equality and a point $x : G \to $ `IntegerScalarCubeBox α S.value`; a grid tuple $u$ in `PrincipalAxisTuples (allocatedGridAxis U b S.value) (allocatedPrincipalSides B U b S)` and a non-grid tuple $v_0$ in `PrincipalAxisTuples (¬ allocatedGridAxis U b S.value) (allocatedPrincipalSides B U b S)`; finite types $O_j$ and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$; finite types $Q_j$; the hypothesis $hb$ that the $\mathbb Z$-span of each $b_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $W_j$ indexed by $Q_j$; a positive natural number $d$; the assumption that each $W_j$ is a full lattice in $V_j$; additively left-invariant probability measures $\nu_j$ on the tori $V_j/W_j$; and for each $j$ and $t \in O_j$ a measurable set $\Omega_{j,t} \subseteq \mathbb R^{J_j}$ contained in the box $\{x : |x_i| < 1/2\}$ (`standardLatticeSmallBox`).
--
--   Let $f$ be a measurable, nonnegative real function on `AllocatedLongJetRows B U b S O`, integrable with respect to `allocatedLongJetReference B U b S O`, such that `allocatedGridlessWeightedKernel B U b S x u v₀ rows d fg f z` $= 0$ for every $z$ outside `mixedCoveredJetRegion U o b d Ω`, where `fg` $=$ `allocatedGridJetDensity B U b hR hσ S x u v₀ rows` (both defined by OpenAI). Let $F : $ `EuclideanJetLayers U O` $\to \mathbb C$ be measurable with $\|F(z)\| \le C$ for all $z$. Then
--   $$\int\!\!\int f(z)\cdot\texttt{allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d}\,(p \mapsto F(p_2))\,(a, z) = \int g(y)\,F(y)\,d\Bigl(\prod_j \prod_{O_j} \nu_j\Bigr)(y),$$
--   where the inner integral is in $z$ against `allocatedLongJetReference B U b S O`, the outer in $a$ against `allocatedFrozenCoefficientSource B U b hR hσ S`, and $g = $ `allocatedCoveredProfileDensity B U b hR hσ S x u v₀ rows hb o bW d Ω f`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_test_integral_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_test_integral` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedRowIdealSupport.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedRowIdealSupport.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_test_integral)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

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
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v₀ rows
local notation "fd" => coefficientDeckJetDensity (B := Q) root dirs rows d

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

omit [Fintype α] in
include hΩm hΩ in
theorem allocatedCoveredProfile_test_integral_s2
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
end
