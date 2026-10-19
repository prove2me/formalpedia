-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedCubeSource_good_kernel_residue_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSlicedCubeSource_good_kernel_residue_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:45:26.8479+00:00
-- url     : https://prove2.me/theorems/f10a1ab2-a502-4488-9238-c2c30fefcbaa
-- title:
--   A large sliced cube source yields a good kernel cube and a residue class on which the sliced tuple value stays large
-- statement:
--   Let $m$ be a natural number and $G$ a finite type with decidable equality. For $j \in \operatorname{Fin} m$ let $I_j$ (with decidable equality) and $J_j$ be finite types and $n_j$ a natural number; let $B$ assign a finite type with decidable equality to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$, let `euclideanSubspace (U j)` be that subspace in the Euclidean space $\mathbb{R}^{J_j}$ (defined by OpenAI), let $b_j$ be a real basis, indexed by $\operatorname{Fin} n_j$, of its orthogonal complement whose integer span equals `projectedIntegerLattice` (the projection of $\mathbb{Z}^{J_j}$ onto that complement; hypothesis hb), and let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$; assume each `latticeSection` (the lattice $\mathbb{Z}^{J_j} \cap$ `euclideanSubspace (U j)`) is a full lattice. Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$, and let $S$ be a `LayerSamplerScale B U b R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $\mathrm{dim}$ be a positive natural number (so $\operatorname{Fin} \mathrm{dim}$ is nonempty), $X$ a finite type, and `poly j` vector polynomials in the variables $X$ with values in $J_j \to \mathbb{R}$ whose coefficients all lie in $U_j$ (hmem).
--
--   Let $N : X \to \mathbb{N}$ with all $N_t > 0$; let $W \ge 0$, $\tau > 0$, $\xi > 0$ be reals; let $\mathrm{stride} : X \to \mathbb{N}$ and let `cells` be a finite set of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride` (residue patterns modulo the strides); write $w$ = `narrowTrimmedSpatialWidths W τ ξ N` (OpenAI's widths), and assume (hmass) $\sum_z$ `selectedResidueSmoothWeight stride cells w z` $> 0$ (the smooth weight of $z$ is OpenAI's product profile of $z/w$ if the residue pattern of $z$ is in `cells`, and $0$ otherwise). Let `bases` be a nonempty finite set of points of $\mathbb{Z}^X$ with (htotal) `selectedJointDensityMass bases stride cells w (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem)` $> 0$ (OpenAI's averaged density mass). Let $H : \texttt{LayerSamplerVariables G I n B} \to \mathbb{N}$ with all $H(k) > 0$, $c$ an integer function on the same index type, and $\mathrm{step}$ a natural number, such that (hsubset) for every $k$ the progression `integerProgressionSupport (c k) step (H k)` (the integers $c(k) + \mathrm{step} \cdot i$, $0 \le i < H(k)$) lies in $[0, L_k)$, where $L_k$ is `S.value` for $k \in G$ and `allocatedPrincipalSides B U b S k` for the other indices. Let `kernelLaw` = `containedProgressionCubeLaw` for side `S.value`, lengths $H$, step $\mathrm{step}$ and starts $c$ on the indices in $G$ (OpenAI's law on $G \to$ `IntegerScalarCubeBox (Fin dim) S.value`: uniform cubes of sizes $H$ embedded in the progressions).
--
--   Assume further: an embedding `selection` $: \operatorname{Fin} \mathrm{dim} \hookrightarrow G$; $\mathrm{dim}(\mathrm{dim} + 2) \le |G|$; a natural number $D > 0$ and reals $\delta > 0$, $\eta > 0$; (hkernel) $M_k \le$ `S.value`, where $M_k$ = `scalarKernelCutoff (Fin dim) G 1 D η` (an explicit natural number of OpenAI); $\mathrm{step} > 0$; $\texttt{S.value} \le D \cdot H(g)$ for every $g \in G$; $f : \mathbb{Z}^X \to \mathbb{C}$ with $\lVert f(u) \rVert \le 1$ for all $u$; (hlarge) $\delta + \eta \le \operatorname{Re}$ `allocatedSlicedCubeSource B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells hmass bases H hH c step f` (OpenAI's complex average of the physical cube site test of $f$ over uniform cubes, bases and the smooth residue law); and a function $q$ assigning a nonzero natural number to each $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`.
--
--   Then there exists $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value` with positive weight under `kernelLaw` and with `GoodScalarKernelTuple selection (1/Mk) Mk x` (OpenAI's predicate: the normalised scalar cube minor of $x$ on `selection` exceeds $1/M_k$ in absolute value, and, by `HasBoundedScalarPeriod`, the range of the integer linear map given by OpenAI's `scalarCubeDifferenceMatrix x` contains $a$ times the whole integer lattice for some natural number $0 < a \le M_k$), and there exists a residue assignment $r$ from `PrincipalTupleIndex B (layerSamplerDegree I n)` to $\mathrm{Option}(\operatorname{Fin} \mathrm{dim}) \to \mathbb{Z}/q(x)$ such that (hr) the cell of principal integer tuples whose residues modulo $q(x)$ equal $r$ has positive mass under `principalTupleWeights` with lengths $H$ on the principal indices, and
--   $$\delta \le \operatorname{Re}\, \mathbb{E}_{y \sim \mathcal{L}}\, \texttt{allocatedSlicedTupleValue B U b hb o hR hsigma S X poly hmem N hN hW htau hxi stride cells hmass bases x y f},$$
--   where $\mathcal{L}$ = `containedSupportedProgressionLaw` with sides `allocatedPrincipalSides B U b S`, lengths $H$, step $\mathrm{step}$, starts $c$ (on the principal indices), modulus $q(x)$ and residues $r$ (OpenAI's law on principal integer tuples), and `allocatedSlicedTupleValue` is OpenAI's complex value of the sliced test at the kernel cube $x$ and principal tuple $y$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSlicedCubeSource_good_kernel_residue_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSlicedCubeSource_good_kernel_residue` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedRowsProjectedSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B214`, `OAIE3v2B217` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedRowsProjectedSource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSlicedCubeSource_good_kernel_residue)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B214
import Definitions.Def_OAIE3v2B217

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

variable (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
variable (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ)
variable (hsubset : ∀ k : LayerSamplerVariables G I n B,
  integerProgressionSupport (c k) (step : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ)
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k : ℕ) : ℤ))

local notation "kernelLaw" => containedProgressionCubeLaw (α := Fin dim)
  (fun _ : G => S.value) (fun g => H (Sum.inl g)) (fun _ => step) (fun g => c (Sum.inl g))
  (fun _ => S.positive) (fun g => hH (Sum.inl g)) (fun g => hsubset (Sum.inl g))

include hbases htotal in

theorem allocatedSlicedCubeSource_good_kernel_residue_s2
    [Nonempty (Fin dim)]
    (selection : Fin dim ↪ G) (hG : dim * (dim + 2) ≤ Fintype.card G)
    {D : ℕ} (hD : 0 < D) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hkernel : scalarKernelCutoff (Fin dim) G 1 D η ≤ S.value)
    (hstep : 0 < step) (hLH : ∀ g, S.value ≤ D * H (Sum.inl g))
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1)
    (hlarge : δ + η ≤ (allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f).re)
    (q : (G → IntegerScalarCubeBox (Fin dim) S.value) → ℕ) [∀ x, NeZero (q x)] :
    let Mk := scalarKernelCutoff (Fin dim) G 1 D η
    ∃ (x : G → IntegerScalarCubeBox (Fin dim) S.value),
      0 < (kernelLaw).weight x ∧ GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (q x))
      (hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r))),
      δ ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
        (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j)) (q x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
