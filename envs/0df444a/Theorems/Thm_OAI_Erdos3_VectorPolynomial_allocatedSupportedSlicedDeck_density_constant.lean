-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedDeck_density_constant
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedDeck_density_constant
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T14:46:11.990092+00:00
-- url     : https://prove2.me/theorems/96a64602-6a91-4fa1-b2b8-642d2030acbf
-- title:
--   The deck jet density is the same at every supported grid tuple
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, $b_j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$, and $S$ a `LayerSamplerScale B U b R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality and `rowSets` $j$ a `Finset (Finset α)` for each $j$; `rows` $j$ is the inclusion of `rowSets j` into `Finset α`. Write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)` and let grid be the predicate `allocatedGridAxis U b S.value` on axes (an axis $\langle j,\mathrm{inr}\,i\rangle$ is a grid axis when `basisAxisScale (b j) i` $\le\texttt{S.value}^{\texttt{layerTailDegree}\ m+1}$; axes $\langle j,\mathrm{inl}\,\_\rangle$ never are). Let $H,\mathrm{step}\colon\mathcal T\to\mathbb N$ with $H_t>0$ (`hH`) and $c\colon\mathcal T\to\mathbb Z$, with `integerProgressionSupport (c t) (step t) (H t)` $=\{c_t+\mathrm{step}_t\,i:0\le i<H_t\}\subseteq[0,\ $`allocatedPrincipalSides B U b S t`$)$ (`hsubset`); let $q\in\mathbb N$ and $r\colon\mathcal T\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, and assume (`hcell`) that the event `principalResidueLabel q y = r` has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`. Let `gridLaw` be `containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c … hH hsubset q r hcell grid`, a `FiniteProbabilityWeights` on `PrincipalAxisTuples grid (allocatedPrincipalSides B U b S)` (tuples over the indices on grid axes). Let $x\colon G\to$ `IntegerScalarCubeBox α S.value`; let $u_0$ be a tuple over the grid indices with nonzero `gridLaw` weight (`hu₀`); let $v_0$ be a tuple over the non-grid indices (`PrincipalAxisTuples (¬grid) (allocatedPrincipalSides B U b S)`); let $Q_j$ ($j\in\mathrm{Fin}\,m$) be finite types and $d\ne0$ a natural number. Assume (`hperiod`) that for every $j$ the lattice $q\,\mathbb Z^{\mathrm{rowSets}\,j}$ (`integerScalarLattice`) is contained in the range of the integer matrix `scalarKernelIntegerJet x (j + 1) (rows j)` acting on vectors. For a grid tuple $u$ put $\mathrm{root}(u)=$ `allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)` and $\mathrm{dirs}(u)=$ `allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)` (the integer vector of `none` coordinates and the integer matrix of `some` coordinates of $x$ and of the joined tuple). Then for every grid tuple $u$ with nonzero `gridLaw` weight and every $z$ assigning an element of $\mathbb Z/d$ to each $j$, each element of `rowSets j` and each element of $Q_j$,
--   $$\texttt{coefficientDeckJetDensity}\ (\mathrm{root}\ u)\ (\mathrm{dirs}\ u)\ \mathrm{rows}\ d\ z=\texttt{coefficientDeckJetDensity}\ (\mathrm{root}\ u_0)\ (\mathrm{dirs}\ u_0)\ \mathrm{rows}\ d\ z,$$
--   where `coefficientDeckJetDensity root A rows d z` is the number of all such $z$ times the probability that `coefficientDeckJetMap root A rows d` sends a uniformly random element of `CoefficientDeckResidues Q d` to $z$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedDeck_density_constant` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedUniformPhysicalSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B135` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedUniformPhysicalSource.lean#L59

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B135

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

include hu₀ hperiod in
theorem allocatedSupportedSlicedDeck_density_constant
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (hu : (gridLaw).weight u ≠ 0) (z : ∀ j, rowTypes j → Q j → ZMod d) :
    coefficientDeckJetDensity (root u) (dirs u) rows d z =
      coefficientDeckJetDensity (root u₀) (dirs u₀) rows d z := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
