-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_mixedCoveredJet_reference_map_s2
-- name    : OAI.Erdos3.VectorPolynomial.mixedCoveredJet_reference_map_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:40:44.718197+00:00
-- url     : https://prove2.me/theorems/0a555570-851a-4bac-917c-c5c89657b9b2
-- title:
--   The mixed covered jet chart pushes the restricted covered jet array reference forward to the restricted product Haar measure
-- statement:
--   Let $m$ be a natural number and, for $j \in \operatorname{Fin} m$, let $I_j, O_j, J_j, E_j$ be finite types and $n_j$ a natural number. Let $U_j$ be a real subspace of $J_j \to \mathbb{R}$, let `euclideanSubspace (U j)` be the same subspace inside the Euclidean space $\mathbb{R}^{J_j}$ (defined by OpenAI), let $o_j$ be an orthonormal basis of it indexed by $I_j$, let $b_j$ be a real basis indexed by $\operatorname{Fin} n_j$ of its orthogonal complement whose integer span equals `projectedIntegerLattice (euclideanSubspace (U j))` (the orthogonal projection of $\mathbb{Z}^{J_j}$ onto that complement) (hb), and let $bW_j$ be a $\mathbb{Z}$-basis indexed by $E_j$ of $\Lambda_j$ = `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the lattice $\mathbb{Z}^{J_j} \cap$ `euclideanSubspace (U j)`), assumed to be a $\mathbb{Z}$-lattice in `euclideanSubspace (U j)`. Let $d$ be a positive natural number. Let $\nu_j$ be a left-invariant probability measure on the torus `euclideanSubspace (U j)` $/ \Lambda_j$. For each $j$ and $t \in O_j$ let $\Omega_{j,t}$ be a measurable subset of $\mathbb{R}^{J_j}$ contained in `standardLatticeSmallBox (J j)` $= \{x : |x_i| < 1/2 \text{ for all } i\}$.
--
--   Let `chart` = `mixedCoveredJetChart U o b hb bW d`, OpenAI's map from `MixedCoveredJetSource I O E n d` (for each $j$ a real array $I_j \to O_j \to \mathbb{R}$ and an integer array $\operatorname{Fin} n_j \to O_j \to \mathbb{Z}$, together with residue arrays $O_j \to E_j \to \mathbb{Z}/d$) to `EuclideanJetLayers U O` (for each $j$ and $t \in O_j$ a point of the torus `euclideanSubspace (U j)` $/\Lambda_j$); let `region` = `mixedCoveredJetRegion U o b d Ω`, the preimage under OpenAI's coordinate map `mixedCoveredJetCoordinates U o d` of `coveredJetSourceRegion U b d Ω`; let $\lambda$ = `coveredJetArrayReference U d`, the product over $j$ of $(\operatorname{covol} \Lambda_j)^{-\#O_j}$ times `mixedArrayReference (I j) (Fin (n j)) (O j)`, times the uniform probability measure on the residue arrays; and let `haar` be the product measure $\prod_j \prod_{t \in O_j} \nu_j$ on `EuclideanJetLayers U O`. Then the pushforward under `chart` of $\lambda$ restricted to `region` equals `haar` restricted to the image `chart '' region`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.mixedCoveredJet_reference_map_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.mixedCoveredJet_reference_map` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredSiteExpansion.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B092`, `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredSiteExpansion.lean (declaration OAI.Erdos3.VectorPolynomial.mixedCoveredJet_reference_map)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set _root_.OAI.Set
open scoped Classical

namespace VectorPolynomial

open Module Submodule

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

include hΩm hΩ

theorem mixedCoveredJet_reference_map_s2 :
    Measure.map chart ((coveredJetArrayReference U d).restrict region) =
      (haar).restrict (chart '' region) := by
  sorry

end VectorPolynomial
end Erdos3

end

end OAI
end
