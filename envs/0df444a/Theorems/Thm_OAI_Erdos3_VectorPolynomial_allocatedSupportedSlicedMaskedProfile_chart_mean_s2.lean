-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedMaskedProfile_chart_mean_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedMaskedProfile_chart_mean_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:43:52.507064+00:00
-- url     : https://prove2.me/theorems/460ad652-9910-4f39-af7d-e1c7bc3e3438
-- title:
--   Averaging the masked covered profile over the supported grid law factors as grid density times the gridless profile
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, and $b_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)` whose $\mathbb{Z}$-span is `projectedIntegerLattice (euclideanSubspace (U j))` (hypothesis $hb$). Let $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U b R σ` (defined by OpenAI, with positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality and $\mathrm{rowSets} : \mathrm{Fin}\ m \to \mathrm{Finset}(\mathrm{Finset}\ \alpha)$; write $\mathrm{rowTypes}_j$ for the subtype of elements of $\mathrm{rowSets}_j$ and $\mathrm{rows}_j : \mathrm{rowTypes}_j \to \mathrm{Finset}\ \alpha$ for the inclusion. Write "grid" for the predicate `allocatedGridAxis U b S.value` on axes, and $\mathrm{sides}$ = `allocatedPrincipalSides B U b S` (both defined by OpenAI).
--
--   **Hypotheses.**
--   - $H, \mathrm{step} :$ `PrincipalTupleIndex B (layerSamplerDegree I n)` $\to \mathbb{N}$ and $c$ to $\mathbb{Z}$, with $H_j > 0$ and `integerProgressionSupport (c j) (step j) (H j)` $= \{c_j + \mathrm{step}_j v : 0 \le v < H_j\}$ contained in $[0, \mathrm{sides}_j)$ for every $j$.
--   - $q \in \mathbb{N}$ and $r :$ `PrincipalTupleIndex B (layerSamplerDegree I n)` $\to \mathrm{Option}\ \alpha \to \mathbb{Z}/q$ such that the residue cell $\{y : \texttt{principalResidueLabel}\ q\ y = r\}$ has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (product weights, defined by OpenAI); call this hypothesis $hcell$.
--   - Let `gridLaw` = `containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) sides H step c _ hH hsubset q r hcell grid` (a probability law on the integer tuples of the grid axes, defined by OpenAI).
--   - $x : G \to$ `IntegerScalarCubeBox α S.value`; $u_0$ a grid-axis tuple (in `PrincipalAxisTuples grid sides`) with nonzero `gridLaw` weight; $v_0$ a non-grid-axis tuple (in `PrincipalAxisTuples (fun a => ¬ grid a) sides`).
--   - $Q : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $d$ a nonzero natural number, and for every $j$ the lattice $q\cdot\mathbb{Z}^{\mathrm{rowTypes}_j}$ (`integerScalarLattice`) is contained in the image of the integer matrix `scalarKernelIntegerJet x (j + 1) (rows j)` (defined by OpenAI).
--   - $o_j$ an orthonormal basis of `euclideanSubspace (U j)` indexed by $I\ j$, and $bW_j$ a $\mathbb{Z}$-basis indexed by $Q_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`.
--   - $f$ a real function on real vectors indexed by $\Sigma_{a \text{ non-grid}}\, \mathrm{rowTypes}_{a_1}$ (where $a_1$ is the layer of the axis $a$).
--   - $z \in$ `MixedCoveredJetSource I rowTypes Q n d` (real and integer coefficient arrays together with residues modulo $d$) lying in the region `mixedCoveredJetRegion U o b d Ω`, where $\Omega_{j,t}$ = `standardLatticeClosedQuarterBox (J j)` $= \{w : |w_i| \le 1/4 \text{ for all } i\}$.
--
--   **Conclusion.** Let `chart` = `mixedCoveredJetChart U o b hb bW d` (a map from `MixedCoveredJetSource` to `EuclideanJetLayers U rowTypes`, defined by OpenAI) and $y_0$ = `principalAxisJoin grid u₀ v₀` (the full tuple joining $u_0$ and $v_0$). Then the `gridLaw`-mean of
--   $$u \mapsto \texttt{allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (principalAxisJoin grid u v₀) q f}\ (\mathrm{chart}\ z)$$
--   equals
--   $$\texttt{allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x}\ (\texttt{allocatedFullGridRowsOfMixed B U b S rowSets}\ z_1) \cdot \texttt{allocatedWholeMaskedGridlessProfile B U b S x}\ y_0\ \texttt{rows hb o bW d q f}\ (\mathrm{chart}\ z),$$
--   where $z_1$ is the coefficient-array component of $z$ and all named functions are defined by OpenAI (respectively: the masked covered profile density of a full tuple, the product of the supported grid probability masses at the grid rows of $z_1$, and the corresponding profile with the grid factors removed).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedMaskedProfile_chart_mean_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedMaskedProfile_chart_mean` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedUniformPhysicalSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B217` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedUniformPhysicalSource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedMaskedProfile_chart_mean)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B217

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
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

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "y₀" => principalAxisJoin grid u₀ v₀
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include hu₀ hperiod in

theorem allocatedSupportedSlicedMaskedProfile_chart_mean_s2
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (z : MixedCoveredJetSource I rowTypes Q n d) (hz : z ∈ region) :
    (gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
      (principalAxisJoin grid u v₀) q f (chart z)) =
    gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) *
      allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
