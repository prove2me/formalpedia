-- Prove2me | Theorems.Thm_OAI_Erdos3_PolynomialPatch_LowestLayerModel_exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2
-- name    : OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:06:01.250826+00:00
-- url     : https://prove2.me/theorems/9af87edc-85e1-45fb-9dc7-74b8d678db89
-- title:
--   Freezing the lowest layer of a polynomial patch on an allocated padded parameter box, under early logarithmic bounds
-- statement:
--   **Setting.** Let $m, q, s, D, E$ be natural numbers with $m \le q$, and let $X, G$ be finite types. Let $L$ be a `RankPreparationFamily X (Fin D) m` (a family of $m$ rank-preparation layers, defined by OpenAI), and write `L.pad q j` ($j \in \mathrm{Fin}\ q$) for its padding to $q$ layers by empty layers; each `L.pad q j` has a finite coordinate type `(L.pad q j).Coord` and a vector polynomial `(L.pad q j).poly`. Let $I, \mathrm{Deck} : \mathrm{Fin}\ q \to \mathrm{Type}$ be families of finite types (the finiteness of $\mathrm{Deck}\ j$ is not assumed), $n : \mathrm{Fin}\ q \to \mathbb{N}$, and $B$ a family of finite types indexed by `LayerSamplerAxis I n` $= \Sigma_{j}\, (I\ j \oplus \mathrm{Fin}\ (n\ j))$. For each $j$ let $U_j$ be a real subspace of $(\texttt{(L.pad q j).Coord}) \to \mathbb{R}$, let $b_j$ be a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ viewed inside Euclidean space) whose $\mathbb{Z}$-span equals `projectedIntegerLattice (euclideanSubspace (U j))` (the orthogonal projection of the standard integer lattice onto that complement), and let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I\ j$. Let $R, \sigma : \mathrm{Fin}\ q \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U b R σ` (a structure defined by OpenAI whose field `S.value` is a positive natural number satisfying certain width and gap conditions). Write $\mathrm{Vars}$ for `LayerSamplerVariables G I n B` $= G \oplus$ `PrincipalTupleIndex B (layerSamplerDegree I n)`, and $\mathrm{sides} : \mathrm{Vars} \to \mathbb{N}$ for the function equal to `S.value` on $G$ and to `allocatedPrincipalSides B U b S` (defined by OpenAI) on the principal tuple indices.
--
--   **Hypotheses.** Let $A$ be a `PolynomialPatch X s (D + E)` (defined by OpenAI: a family of weighted polynomial slots in variables $X$ together with a patch kernel with Lipschitz constant `A.kernel.lip`, and a real-valued function `A.value` on $X \to \mathbb{R}$), and let $F$ be a `A.LowestLayerModel m` (a description of the first $D$ slots of $A$ by a strictly lower-triangular matrix and origin polynomials of degree at most $m$, defined by OpenAI), with normalized origin `F.normalizedOrigin`. Suppose:
--
--   - $ip : \mathrm{Fin}\ D \to \mathbb{Z}[X]$ with total degree of each $ip\ i$ at most $m$; $c_0 \in \mathbb{R}^{\mathrm{Fin}\ D}$; $err$ a vector polynomial on $X$ with values in $\mathbb{R}^{\mathrm{Fin}\ D}$; and the vector polynomial with coordinates `F.normalizedOrigin` (in the standard basis) equals `L.polynomial + integerCoordinates ip + (1 ⊗ c₀) + err`, where `integerCoordinates ip` is $ip$ viewed as a real vector polynomial and $1 \otimes c_0$ is the constant $c_0$;
--   - for all $j$ and all $d$, the coefficient `coefficients (L.pad q j).poly d` lies in $U_j$; and for all $j$, `(L.pad q j).poly` has degree at most $j + 1$ (with every variable of weight $1$);
--   - $\sigma_j \le 1$ for all $j$; $C : \mathrm{Fin}\ q \to \mathbb{R}$ with $C_j \ge 0$, and for all $j$ and $v$, $\lVert \phi_j^{-1}(v) \rVert \le C_j \lVert v \rVert$, where $\phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` (the linear chart sending a vector to its projection onto the subspace together with its normalized coordinates in $b_j$);
--   - $c_j \in U_j$ for each $j$; $N : X \to \mathbb{N}$ with $N\ x > 0$ for all $x$;
--   - real numbers $\tau, \xi$ with $0 < \tau \le 1/2$, $\xi \le 1$, and $4 \le \tau N(x)$ for every $x$;
--   - a pair $z = (z_1, z_2)$ with $z_1$ in `trimmedIntegerBox N (spatialTrimMargin τ N)` (the integer box $\prod_x [0, N x)$ trimmed by the margin $\lceil \tau N(x)/4 \rceil$ on each side) and $z_2$ in `rectangularWeightIndices 0 W 1`, where $W$ = `narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N` (explicit width functions defined by OpenAI);
--   - `sample : CoefficientSamplerArrays I n` and `read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ` such that `AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ (fun j => (L.pad q j).poly) hm c z.1 z.2 sample read` holds (a predicate defined by OpenAI saying that `read` records the integer frame determined by $z$ and recovers the coefficient sample `sample`);
--   - real numbers $\delta, \mathrm{gain}$ with $\delta \ge 0$, $0 < \mathrm{gain} \le 1$, and $|err(x)_i| \le \delta$ for every $x$ in `integerBox N` (the box $\prod_x [0, N x) \cap \mathbb{Z}$) and every $i$;
--   - real numbers $p, P_{\mathrm{early}}$ with $p \ge 0$, $D \le e^{p}$, $q \le e^{p}$, `A.kernel.lip` $\le e^{p}$, $|\texttt{(L.pad q j).Coord}| \le e^{p}$ and $C_j \le e^{p}$ for all $j$, $e^{-p} \le \mathrm{gain}$, $\delta \le e^{-(3p + 130)}$, and $6p + 35 \le P_{\mathrm{early}}$;
--   - for every $C' : \mathrm{Fin}\ q \to \mathbb{R}$ with $0 \le C'_j \le e^{P_{\mathrm{early}}}$ for all $j$, one has $C'_j\,(|I\ j| + 1)\,R_j \le 1/4$ for all $j$;
--   - a function $\mathrm{score}$ on `integerBox sides` with $|\mathrm{score}(u)| \le 1$ for all $u$, and
--   $$\frac{\mathrm{gain}}{2} \le \mathbb{E}_{u}\ \mathrm{score}(u)\cdot \texttt{A.value}\Bigl(x \mapsto F_{\mathrm{none}}(x) + \sum_{k \in \mathrm{Vars}} F_k(x)\, u_k\Bigr),$$
--   where the expectation is the uniform average over $u \in$ `integerBox sides`, $F_{\mathrm{none}}(x) = z_1(x) + z_2(\mathrm{none}, x)$ and $F_k(x) = z_2(\mathrm{some}\ k, x)$ (this is `integerAffineMap` applied to `jointIntegerFrame (z.1, z.2)`).
--
--   **Conclusion.** There is a `PolynomialPatch Vars s E` $A'$ with `A'.kernel.lip = A.kernel.lip`, with `A'.weight i = A.weight (D + i)` for every $i \in \mathrm{Fin}\ E$, and with
--   $$\frac{7\,\mathrm{gain}}{16} \le \mathbb{E}_{u}\ \mathrm{score}(u)\cdot \texttt{A'.value}(k \mapsto u_k),$$
--   the expectation again being the uniform average over $u \in$ `integerBox sides`.
--
--   Lean: `OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2`, which states OpenAI's `OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_freeze_allocated_padded_parameter_box_of_early_bounds` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedPaddedParameterBoxEarlyFreeze.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B229`, `OAIE3v2B230` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedPaddedParameterBoxEarlyFreeze.lean (declaration OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_freeze_allocated_padded_parameter_box_of_early_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B229
import Definitions.Def_OAIE3v2B230

section

namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
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

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2
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
    (score : integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) → ℝ) (hscoreBound : ∀ u, |score u| ≤ 1)
    (hscore : gain / 2 ≤ 𝔼 u, score u * A.value
      (fun x => (integerAffineMap (fun x k => jointIntegerFrame (z.1.val,z.2.val) (some k) x)
        (jointIntegerFrame (z.1.val,z.2.val) none) u.val x : ℝ))) :
    ∃ A' : PolynomialPatch Vars s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      7 * gain / 16 ≤ 𝔼 u, score u * A'.value (fun k => (u.val k : ℝ)) := by
  sorry

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
end
