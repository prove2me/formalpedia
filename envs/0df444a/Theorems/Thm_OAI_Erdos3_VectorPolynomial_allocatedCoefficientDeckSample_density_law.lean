-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoefficientDeckSample_density_law
-- name    : OAI.Erdos3.VectorPolynomial.allocatedCoefficientDeckSample_density_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:07:35.254657+00:00
-- url     : https://prove2.me/theorems/1606299a-ae1b-498e-af83-22a90e4e4d8c
-- title:
--   The allocated coefficient deck sample has the allocated coefficient density on the torus
-- statement:
--   The statement uses these section variables. Let $m \in \mathbb{N}$, $G$ a finite type, $I_j$ and $J_j$ ($j \in \mathrm{Fin}\ m$) finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, and $B_a$ finite types indexed by $a \in$ `LayerSamplerAxis I n` $= \Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$; write $K$ = `LayerSamplerVariables G I n B` (OpenAI's index type of sampler variables). Let $U_j \subseteq \mathbb{R}^{J_j}$ be real subspaces, $W_j$ = `euclideanSubspace (U j)` the corresponding subspace of Euclidean space $\mathbb{R}^{J_j}$, and $\Lambda_j$ = `latticeSection (standardEuclideanLattice (J j)) (W j)` $= \mathbb{Z}^{J_j} \cap W_j$, assumed to be a full-rank lattice in $W_j$. Let $\mathrm{basis}_j$ be a real basis of $W_j^\perp$ indexed by $\mathrm{Fin}(n_j)$ whose $\mathbb{Z}$-span is `projectedIntegerLattice (W j)` (the image of $\mathbb{Z}^{J_j}$ in $W_j^\perp$) (hypothesis $hb$); $o_j$ an orthonormal basis of $W_j$ indexed by $I_j$; $Q_j$ finite types and $bW_j$ a $\mathbb{Z}$-basis of $\Lambda_j$ indexed by $Q_j$; $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with all $R_j > 0$ and $\sigma_j > 0$; $S$ a `LayerSamplerScale B U basis R σ` (OpenAI's structure: a positive natural number $S.\mathrm{value}$ satisfying width and gap conditions); and $d$ a positive natural number. Let the coefficient torus `CoefficientTorus U` (over $K$) be compact with its Borel $\sigma$-algebra, $\mu$ an add-left-invariant probability measure on it, and $\nu_j$ add-left-invariant probability measures on $W_j/\Lambda_j$. Now assume $\sigma_j \le 1$ for all $j$, and let $C : \mathrm{Fin}\ m \to \mathbb{R}$ with $C_j \ge 0$, $\|\Phi_j^{-1}(z)\| \le C_j\|z\|$ for all $j$ and $z$, where $\Phi_j$ = `normalizedOrthogonalChart (W j) (basis j)` (a continuous linear isomorphism of Euclidean $\mathbb{R}^{J_j}$ with $W_j \times \mathbb{R}^{n_j}$), and $C_j(|I_j| + 1)R_j \le 1/4$ for all $j$. Then `CoefficientDeckDensityLaw U bW basis hb o μ source density d` holds, with source = `allocatedCoefficientSource B U basis hR hσ S` (OpenAI's product measure of mixed scalar array laws on the coefficient sampler arrays) and density = `allocatedCoefficientDensity B U basis hb o hR hσ S` (a real function on the coefficient torus). That predicate says: the push-forward of source $\times$ (uniform measure on the finite set `CoefficientDeckResidues B d`) under OpenAI's map `canonicalCoefficientDeckSample U bW basis hb o d` equals the measure with density $y \mapsto \mathrm{density}(\pi_d(y))$ with respect to $\mu$, where $\pi_d$ is `quotientIntegerCover (coefficientIntegerLattice U) d`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedCoefficientDeckSample_density_law` in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedProgressionDensityIdentity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B136` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedProgressionDensityIdentity.lean#L170

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

include ν in
theorem allocatedCoefficientDeckSample_density_law
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ C j * ‖z‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) :
    CoefficientDeckDensityLaw U bW basis hb o μ source density d := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
