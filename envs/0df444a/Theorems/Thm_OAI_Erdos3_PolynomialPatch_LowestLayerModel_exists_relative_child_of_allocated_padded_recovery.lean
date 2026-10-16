-- Prove2me | Theorems.Thm_OAI_Erdos3_PolynomialPatch_LowestLayerModel_exists_relative_child_of_allocated_padded_recovery
-- name    : OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_relative_child_of_allocated_padded_recovery
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:22:01.691083+00:00
-- url     : https://prove2.me/theorems/e923e630-8a6d-4ec3-a33b-faaf6b2744d0
-- title:
--   An allocated padded recovered sample with a patch score gives a relative child slice
-- statement:
--   Fix the section data: natural numbers $m, q, s, D, E$ with $m \le q$ (hypothesis `hmq`); finite types $X$ and $G$ with $G$ nonempty; a `RankPreparationFamily X (Fin D) m` $L$ (a family of $m$ rank-preparation layers, each a structure carrying a finite coordinate type `Coord` and a vector polynomial `poly` on $X$ with values in $\mathbb R^{\mathrm{Coord}}$); finite types $I_j$ and types $\mathrm{Deck}_j$ for $j \in \mathrm{Fin}\,q$; $n : \mathrm{Fin}\,q \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); real subspaces $U_j$ of $\mathbb R^{\mathrm{Coord}_j}$, where $\mathrm{Coord}_j$ is the coordinate type of layer $j$ of `L.pad q` (the family padded to length $q$ by empty layers); bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)` whose $\mathbb Z$-span is `projectedIntegerLattice (euclideanSubspace (U j))` (hypothesis $hb$); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; reals $R_j, \sigma_j$ with a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); and $R_j > 0$, $\sigma_j > 0$ for all $j$ (hypotheses $hR$, $h\sigma$). Write $\mathrm{Vars}$ for `LayerSamplerVariables G I n B` and $\mathrm{sides} : \mathrm{Vars} \to \mathbb N$ for the function that is $S.\mathrm{value}$ on the $G$ coordinates and `allocatedPrincipalSides B U b S` on the principal coordinates.
--
--   Let $A$ be a `PolynomialPatch X s (D + E)` (weights in $[1,s]$, polynomial slots, and a kernel with Lipschitz constant $A.\mathrm{kernel.lip}$) and $F$ an `A.LowestLayerModel m` (a structure giving a strictly upper-triangular real matrix, origin polynomials of degree at most $m$, and saying that the first $D$ weights of $A$ equal $m$). Let $ip : \mathrm{Fin}\,D \to \mathbb Z[X]$ with total degrees at most $m$, $c_0 \in \mathbb R^D$, and a vector polynomial $\mathrm{err}$ on $X$ with values in $\mathbb R^D$, such that the vector polynomial with coordinates `F.normalizedOrigin` equals `L.polynomial` $+$ `integerCoordinates ip` $+ (1 \otimes c_0) + \mathrm{err}$. Assume: every coefficient of $(L.\mathrm{pad}\ q)_j.\mathrm{poly}$ lies in $U_j$; $(L.\mathrm{pad}\ q)_j.\mathrm{poly}$ has degree at most $j+1$ (`DegreeLE 1 (j+1)`); $\sigma_j \le 1$; $C : \mathrm{Fin}\,q \to \mathbb R$ with $C_j \ge 0$ and $\|\phi_j^{-1}(v)\| \le C_j \|v\|$ for all $j, v$, where $\phi_j$ is `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`; $c_j \in U_j$; $N : X \to \mathbb N$ with $N_x > 0$; reals $\tau, \xi$ with $0 < \tau \le 1/2$, $\xi \le 1$ and $4 \le \tau N_x$ for all $x$. Let $z$ be a pair of a point of `trimmedIntegerBox N (spatialTrimMargin τ N)` and a point of `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1` with $W =$ `allocatedPhysicalRootBudget B U b S 0`; let `sample : CoefficientSamplerArrays I n` and $\mathrm{read} :$ `AllocatedActualCoefficientIndex G X I Deck n B` $\to \mathbb Z$ satisfy `AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ (j ↦ (L.pad q j).poly) hm c z.1 z.2 sample read` (a conjunction of identities and bounds relating the read-off integers, the sample arrays and the polynomials). Let $\delta \ge 0$ and $0 < \mathrm{gain} \le 1$, with $|\mathrm{err}(x)_i| \le \delta$ for all $x \in$ `integerBox N` and all $i$. Let $p \ge 0$ and $P_{\mathrm{early}}$ be reals with $D, q, A.\mathrm{kernel.lip} \le e^p$, $|\mathrm{Coord}_j| \le e^p$ and $C_j \le e^p$ for all $j$, $e^{-p} \le \mathrm{gain}$, $\delta \le e^{-(3p + 130)}$, $6p + 35 \le P_{\mathrm{early}}$, and such that every $C' : \mathrm{Fin}\,q \to \mathbb R$ with $0 \le C'_j \le e^{P_{\mathrm{early}}}$ for all $j$ satisfies $C'_j (|I_j| + 1) R_j \le 1/4$ for all $j$. Let $n_0, \mathrm{stage}, d_0$ be natural numbers, $\mathrm{discount}$ real and $\mathrm{cutoff}, \mathrm{cost} : \mathbb R \to \mathbb R$ with `RelativePatchInductionRule s n₀ stage discount cutoff cost`; let $p_{\mathrm{child}}, a, \Lambda$ be reals with $p \ge 2$, $p + 2 \le p_{\mathrm{child}}$, $e^{-p} \le a \le \Lambda \le 1$ and `RelativePatchAbsoluteRule s n₀ p a Λ d₀` (both are propositions of OpenAI asserting that `RelativePatchSliceConclusion` holds under stated hypotheses); assume $|\mathrm{Vars}| \le p_{\mathrm{child}}$. Let $H \le S.\mathrm{value}$ be a natural number with $e^{\mathrm{cutoff}(p_{\mathrm{child}})} \le H$; assume $D > 0$, $m < A.\mathrm{weight}(D + i)$ for all $i \in \mathrm{Fin}\,E$, `relativePatchComplexity A` $\le p_{\mathrm{child}}$ (this complexity is $(D+E) + \log(1 + A.\mathrm{kernel.lip})$) and `relativePatchDistinctWeights A` $\le \mathrm{stage} + 1$ (the number of distinct weights). Finally let $f : (\mathrm{Vars} \to \mathbb Z) \to \mathbb R$ take values in $[0,1]$ on `integerBox sides`, with $\{x \in \mathrm{integerBox\ sides} : f(x) \ne 0\}$ free of $(s+2)$-term progressions (`IntegerVectorAPFree`: for all $a$ and all $d \ne 0$ some $a + i d$, $i < s+2$, lies outside the set), and
--   $$\mathrm{gain}/2 \le \mathop{\mathbb E}_{u \in \mathrm{integerBox\ sides}} (f(u) - a)\, A.\mathrm{value}\bigl(\mathrm{jointIntegerPhysicalSite}(u, (z_1, z_2))\bigr).$$
--   Then there is $\mathrm{fixed} : \{k \in \mathrm{Vars} : \neg (H \le \mathrm{sides}_k)\} \to \mathbb Z$ with $0 \le \mathrm{fixed}_k < \mathrm{sides}_k$ for all $k$, such that `RelativePatchSliceConclusion s` holds for the sides $\mathrm{sides}_k$ on $\{k : H \le \mathrm{sides}_k\}$, the function $x \mapsto f(\mathrm{finiteSplitPoint}(x, \mathrm{fixed}))$ (the point equal to $x$ on the large coordinates and to $\mathrm{fixed}$ on the others), target $(1 - \mathrm{discount})^{\mathrm{stage}+1} \Lambda$, rank bound $d_0 + sE$ and cost $\mathrm{cost}(p_{\mathrm{child}})$; that is, there exist $q' > 0$, a `ResidueBoxSlice` $S'$ of modulus $q'$, $d$ and a `PolynomialPatch` $A'$ of rank $d$ such that every side length of $S'$ is at least $e^{-\mathrm{cost}}$ times the corresponding side, $d \le d_0 + sE$, `relativePatchComplexity A'` $\le \mathrm{cost}$, and $e^{-\mathrm{cost}} \le$ `relativePatchSliceScore S' f' target A'`.
--
--   Lean: `OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_relative_child_of_allocated_padded_recovery` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductivePaddedRelativeInitialization.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B072` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductivePaddedRelativeInitialization.lean#L32

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B072

namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily X (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_relative_child_of_allocated_padded_recovery
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c z.1.val z.2.val sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (A.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff cost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p+2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < A.weight (i.natAdd D))
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage+1)
    (f : (Vars → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox sides, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox sides ∧ f x ≠ 0} (s+2))
    (hscore : gain / 2 ≤ 𝔼 u : integerBox sides, (f u.val-a) * A.value
      (fun x => (jointIntegerPhysicalSite u.val (z.1.val,z.2.val) x : ℝ))) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed))
        ((1-discount) ^ (stage+1) * Λ) (d₀+s*E) (cost pchild) := by
  sorry

end Erdos3.PolynomialPatch.LowestLayerModel
end
end OAI
