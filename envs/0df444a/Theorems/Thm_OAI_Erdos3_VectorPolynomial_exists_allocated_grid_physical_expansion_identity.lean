-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_grid_physical_expansion_identity
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_grid_physical_expansion_identity
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T10:12:06.961961+00:00
-- url     : https://prove2.me/theorems/044693eb-2685-4677-84ec-3bc873856e48
-- title:
--   The full-grid chart model expands into Lipschitz physical grid factors
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; a natural number $\mathrm{dim}$, with row sets $\mathrm{rowSets}_j = $ `boundedBooleanJetRows (Fin dim) (j+1)` (subsets of $\mathrm{Fin}\,\mathrm{dim}$ of size at most $j+1$), row types $\mathrm{rowTypes}_j$ and $\mathrm{rows}_j$ their inclusion into $\mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim})$; finite types $E_j$; a point $x : G \to $ `IntegerScalarCubeBox (Fin dim) L_S`; a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`; natural numbers $q$, $d \neq 0$, $\mathrm{period} \neq 0$; $r \in \mathbb R_{\ge 0}$ with $r > 0$; $hb$: the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j` for every $j$; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $E_j$; and $e$ assigning to each grid axis $a$ (an axis satisfying `allocatedGridAxis U b L_S`) a `ScalarSiteExpansion (Finset (Fin dim))` (a structure bundling a finite term type, periods, complex coefficients and factor functions).
--
--   Assume $R_j > 0$ for every $j$; let $N_t, V, C_c, H_s$ be real functions on the grid axes and $L \in \mathbb R_{\ge 0}$ with `(e a).Bounds (Nt a) (V a) (Cc a) L (Hs a)` for every grid axis $a$ (at most $N_t(a)$ terms, positive periods $\le V(a)$, coefficient $\ell^1$-norm $\le C_c(a)$, factors of norm $\le 1$, $L$-Lipschitz, vanishing for $|x| \ge H_s(a)$); $Q \in \mathbb R_{\ge 0}$ with $8\,(|\texttt{layerIntegerPrincipalSlots B}\ (\texttt{allocatedGridIntegerAxis B U b S a})| + 1) \le Q$ for every grid axis $a$; $C_{\mathrm{forward}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\texttt{normalizedOrthogonalChart}\ V_j\ b_j\ v\| \le C_{\mathrm{forward}}(j)\|v\|$; $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1}v\| \le C_j\|v\|$ and $(|\mathrm{rowSets}_j|+1)\,|\mathcal P(\mathrm{Fin}\,\mathrm{dim})|\,C_j(|I_j|+1)\,2rR_j \le 1/4$; a finite type $T$ with $a : T \to \mathbb C$ and $f : T \to \mathcal P(\mathrm{Fin}\,\mathrm{dim}) \to (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$; and, for a type $X$, vector polynomials $p_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` of total degree at most $j+1$ (`DegreeLE 1 (j+1)`) whose coefficients all lie in $U_j$ ($hm$).
--
--   Then there exists $g$ assigning to each choice $k$ of one term of every `e a` and each site $s \in \mathcal P(\mathrm{Fin}\,\mathrm{dim})$ a function $g_{k,s} : (\Sigma_j J_j \to \mathbb R/\mathbb Z) \to \mathbb C$, such that each $g_{k,s}$ is Lipschitz with constant $\max\bigl(\#\text{grid axes}\cdot L\cdot Q\cdot K\sum_j C_{\mathrm{forward}}(j)|J_j|\cdot \pi_k,\ 4\pi_k\bigr)$, where $\pi_k = $ `commonSitePeriod e k` $= \prod_a$ (period of the term $k_a$ of `e a`), and $\|g_{k,s}(v)\| \le 1$ for all $v$; and `AllocatedGridPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g` holds. The latter is OpenAI's identity: for every integer sample $v : X \to (\mathrm{Unit} \oplus \mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z$, at the physical row sample $Y = $ `BooleanCubeKernel.physicalCubeRowSample U d rows p hm v`,
--   $$\Phi(Y)\cdot\texttt{allocatedFullGridChartModel B U b S rowSets d hb o bW e}(Y) = \Phi(Y)\cdot\sum_k \texttt{coverSiteCoefficient e k}\prod_s g_{k,s}\bigl(\texttt{physicalGridFactorInput}\ \pi_k\ p\ (\text{vertex values of } v \text{ at } s)\bigr),$$
--   with $\Phi = $ `allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_grid_physical_expansion_identity` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteModelPhysicalExpansion.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B198` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteModelPhysicalExpansion.lean#L560

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {O J : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_grid_physical_expansion_identity
    (hR : ∀ j, 0 < R j)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) *
      (Fintype.card (Finset (Fin dim)) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) :
    ∃ g : (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      AllocatedGridPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
