-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedMaskedCoveredFactor_mean
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedMaskedCoveredFactor_mean
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T06:22:21.695892+00:00
-- url     : https://prove2.me/theorems/eeeb6757-a301-4b52-b441-ab00f60ad014
-- title:
--   Grid-law mean of the covered fixed factor times a long profile density
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ with decidable equality and finite families $\mathrm{rowSets}_j$ of finsets of $\alpha$, with rowTypes$_j$ the subtype of $\mathrm{rowSets}_j$ and rows$_j$ its inclusion into finsets of $\alpha$. Let grid be the predicate `allocatedGridAxis U b S.value` on axes and FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`. Let $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $c : \mathrm{FullInput} \to \mathbb Z$ with $H_j > 0$ (hH) and each progression `integerProgressionSupport (c j) (step j) (H j)` $= \{c_j + \mathrm{step}_j k : 0 \le k < H_j\}$ contained in $[0,$ `allocatedPrincipalSides B U b S j`$)$ (hsubset); let $q \in \mathbb N$ and $r : \mathrm{FullInput} \to \mathrm{Option}\,\alpha \to \mathbb Z/q$ such that the residue cell $\{y : \texttt{principalResidueLabel q y} = r\}$ has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (the product of uniform scalar-cube weights) (hcell). Let gridLaw be `containedSupportedProgressionAxisLaw … H step c … hH hsubset q r hcell grid` (finite probability weights on the integer tuples `PrincipalAxisTuples grid (allocatedPrincipalSides B U b S)` over grid axes). Let $x : G \to$ `IntegerScalarCubeBox α S.value`; let $u_0$ be a grid tuple of nonzero gridLaw weight (hu₀) and $v_0$ a tuple on the non-grid axes; let $Q_j$ be finite types and $d \ne 0$ a natural number; and assume (hperiod) that for every $j$ the lattice $q\,\mathbb Z^{\mathrm{rowTypes}_j}$ (`integerScalarLattice`) is contained in the range of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)`.
--
--   For every $f : \mathbb R^{\Sigma_{a\ \text{non-grid}}\,\mathrm{rowTypes}_{\mathrm{layer}(a)}} \to \mathbb R$, every $z$ assigning to each $j$ a pair in $\mathbb R^{I_j \times \mathrm{rowTypes}_j} \times \mathbb Z^{\mathrm{Fin}(n_j) \times \mathrm{rowTypes}_j}$, and every $\mathrm{deck}_j : \mathrm{rowTypes}_j \to Q_j \to \mathbb Z/d$, writing $\hat z = (a \mapsto \texttt{coefficientJetAxisEquiv}(z)(a))$, $\mathrm{residue}(u) = (j \mapsto$ `allocatedNonkernelJetMatrix B U b S x u rows j v₀` reduced mod $q)$, $\mathrm{root}(u) =$ `allocatedPhysicalCubeRoot B U b S 0 x (principalAxisJoin grid u v₀)` and $\mathrm{dirs}(u) =$ `allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)`, the gridLaw mean over $u$ of
--   `allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck` $\cdot$ `allocatedLongProfileDensity B U b S x rows q (residue u) f ẑ`
--   equals
--   $$\frac{\texttt{allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x}\ \hat z \cdot \texttt{coefficientDeckJetDensity}(\mathrm{root}(u_0), \mathrm{dirs}(u_0), \mathrm{rows}, d, \mathrm{deck})}{\texttt{coveredJetArrayScale U}} \cdot \texttt{allocatedLongProfileDensity B U b S x rows q (residue u₀) f}\ \hat z,$$
--   where `coveredJetArrayScale U` is $\prod_j \mathrm{covol}(\texttt{latticeSection}\ldots)^{-|\mathrm{rowTypes}_j|}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedMaskedCoveredFactor_mean` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedUniformPhysicalSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B177` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedUniformPhysicalSource.lean#L160

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B177

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

include hu₀ hperiod in
theorem allocatedSupportedSlicedMaskedCoveredFactor_mean
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (z : ∀ j, (I j → rowTypes j → ℝ) × (Fin (n j) → rowTypes j → ℤ))
    (deck : ∀ j, rowTypes j → Q j → ZMod d) :
    (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck *
      allocatedLongProfileDensity B U b S x rows q (residue u) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val)) =
    (allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) *
      coefficientDeckJetDensity (root u₀) (dirs u₀) rows d deck / coveredJetArrayScale (O := rowTypes) U) *
      allocatedLongProfileDensity B U b S x rows q (residue u₀) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
