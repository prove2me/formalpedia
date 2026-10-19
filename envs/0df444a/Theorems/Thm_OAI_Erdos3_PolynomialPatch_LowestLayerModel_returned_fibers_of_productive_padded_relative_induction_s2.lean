-- Prove2me | Theorems.Thm_OAI_Erdos3_PolynomialPatch_LowestLayerModel_returned_fibers_of_productive_padded_relative_induction_s2
-- name    : OAI.Erdos3.PolynomialPatch.LowestLayerModel.returned_fibers_of_productive_padded_relative_induction_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:56:24.677364+00:00
-- url     : https://prove2.me/theorems/92412a3a-473a-478e-a943-33d3946e56a1
-- title:
--   Productive allocated paths return fibers satisfying the relative patch slice conclusion, given a relative patch induction rule
-- statement:
--   **Setting.** Let $m, q, s, D, E, n_X$ be natural numbers with $m \le q$, and let $G$ be a finite nonempty type. Let $L$ be a `RankPreparationFamily (Fin nX) (Fin D) m` (a family of $m$ rank-preparation layers defined by OpenAI; each layer has a finite coordinate type `Coord` and a vector polynomial `poly` in the variables $\operatorname{Fin} n_X$ with values in $\mathrm{Coord} \to \mathbb{R}$), and let `L.pad q` be its padding to $q$ layers by empty layers (defined by OpenAI). For $j \in \operatorname{Fin} q$ let $I_j$ be a finite type, $\mathrm{Deck}_j$ a type and $n_j$ a natural number; let $B$ assign a finite type to each element of `LayerSamplerAxis I n` (the type of pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $(\texttt{L.pad q j}).\mathrm{Coord} \to \mathbb{R}$, let `euclideanSubspace (U j)` be that subspace viewed in Euclidean space (defined by OpenAI), let $b_j$ be a real basis, indexed by $\operatorname{Fin} n_j$, of its orthogonal complement whose integer span equals `projectedIntegerLattice` (the orthogonal projection of the standard integer lattice onto that complement; defined by OpenAI), and let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$. Let $R, \sigma : \operatorname{Fin} q \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U b R σ` (a structure defined by OpenAI; it contains a positive natural number `S.value` with width and gap conditions). Write $\mathrm{Vars}$ for `LayerSamplerVariables G I n B` (a finite index type of sampler variables, defined by OpenAI).
--
--   **Data and hypotheses.** Let `oldPatch` be a `PolynomialPatch (Fin nX) s (D + E)` (OpenAI's structure: weights in $[1, s]$, monotone, polynomial slots and a kernel with a Lipschitz constant `kernel.lip`), and let $F$ be a `LowestLayerModel m` of `oldPatch` (OpenAI's structure; `F.normalizedOrigin` is a $D$-tuple of real polynomials). Assume:
--
--   - $ip : \operatorname{Fin} D \to \mathbb{Z}[x_1, \dots, x_{n_X}]$ with every $ip_i$ of total degree at most $m$; $c_0 \in \mathbb{R}^D$; $err$ a vector polynomial in $\operatorname{Fin} n_X$ with values in $\mathbb{R}^D$; and the identity `ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin` $=$ `L.polynomial` $+$ `integerCoordinates ip` $+ (1 \otimes c_0) + err$, where `L.polynomial` is the sum of the layer polynomials of $L$ copied into $\mathbb{R}^D$ along their labels and `integerCoordinates ip` is $ip$ viewed as a real vector polynomial (both defined by OpenAI).
--   - (hm) every coefficient of each `(L.pad q j).poly` lies in $U_j$; (hp) each `(L.pad q j).poly` has total degree at most $j+1$.
--   - $\sigma_j \le 1$ for all $j$; $C : \operatorname{Fin} q \to \mathbb{R}$ with $C_j \ge 0$, and $\lVert \Phi_j^{-1}(v) \rVert \le C_j \lVert v \rVert$ for all $j$ and $v$, where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` (OpenAI's linear isomorphism of the ambient space with `euclideanSubspace (U j)` $\times \mathbb{R}^{n_j}$).
--   - $N : \operatorname{Fin} n_X \to \mathbb{N}$, real $\tau \le 1/2$ and $\xi \le 1$, with $4 \le \tau N_x$ for every $x$.
--   - $\mathrm{stride} : \operatorname{Fin} n_X \to \mathbb{N}$, a finite set `cells` of `ColumnResiduePattern (Option Vars) (Fin nX) stride` (residue patterns: an element of $\mathbb{Z}/\mathrm{stride}_x$ for each pair in $\mathrm{Option}\ \mathrm{Vars} \times \operatorname{Fin} n_X$), and `center` in `CoefficientTorus U` (OpenAI's coefficient torus).
--   - $A$ a proof of `AllocatedExternalCandidateSampler B U b S hb o hR hσ N (fun j => (L.pad q j).poly) hm τ ξ stride cells center` (OpenAI's proposition packaging positivity and nonemptiness conditions on this sampler); it provides the path type `A.Path` (pairs of a base point in a trimmed integer box and a rectangular weight index), the side lengths `A.sides : Vars → ℕ`, the widths `A.widths` and the base set `A.bases`.
--   - `centerLift` $\in \prod_j U_j$; a finite set `productive` of paths in `A.Path`; for each $z \in$ `productive`, arrays `sample z` in `CoefficientSamplerArrays I n` and an integer function `read z` on `AllocatedActualCoefficientIndex G (Fin nX) I Deck n B` (both index types defined by OpenAI), such that `AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ (fun j => (L.pad q j).poly) hm centerLift` holds at the two components of $z$, `sample z` and `read z` (an OpenAI predicate saying the read noise and the canonical coefficient sample are recovered from the path).
--   - Reals $\delta \ge 0$ and $0 < \mathrm{gain} \le 1$, with $|err(x)_i| \le \delta$ for every $x$ in `integerBox N` (the integer box $\prod_x [0, N_x)$) and every $i$.
--   - Reals $p \ge 0$ and $P_{\mathrm{early}}$ with $D \le e^p$, $q \le e^p$, `oldPatch.kernel.lip` $\le e^p$, $|(\texttt{L.pad q j}).\mathrm{Coord}| \le e^p$ and $C_j \le e^p$ for all $j$, $e^{-p} \le \mathrm{gain}$, $\delta \le e^{-(3p + 130)}$, $6p + 35 \le P_{\mathrm{early}}$, and: for every $C' : \operatorname{Fin} q \to \mathbb{R}$ with $0 \le C'_j \le e^{P_{\mathrm{early}}}$ for all $j$, one has $C'_j\,(|I_j| + 1)\,R_j \le 1/4$ for all $j$.
--   - Natural numbers $n_0, \mathrm{stage}, d_0$, a real $\mathrm{discount}$ and functions $\mathrm{cutoff}, \mathrm{childCost} : \mathbb{R} \to \mathbb{R}$ such that `RelativePatchInductionRule s n₀ stage discount cutoff childCost` holds (OpenAI's predicate: an inductive rule producing `RelativePatchSliceConclusion` on boxes from a patch of bounded complexity and stage).
--   - Reals $p_{\mathrm{child}}, a, \Lambda$ with $2 \le p$, $p + 2 \le p_{\mathrm{child}}$, $e^{-p} \le a \le \Lambda \le 1$, and `RelativePatchAbsoluteRule s n₀ p a Λ d₀` (OpenAI's predicate: the base case of the relative patch argument on prime boxes).
--   - $|\mathrm{Vars}| \le p_{\mathrm{child}}$; a natural number $H$ with $H \le$ `S.value` and $e^{\mathrm{cutoff}(p_{\mathrm{child}})} \le H$; $0 < D$; `oldPatch.weight (D + i)` $> m$ for every $i \in \operatorname{Fin} E$; `relativePatchComplexity oldPatch` $\le p_{\mathrm{child}}$ (this complexity is the number of slots plus $\log(1 + \texttt{kernel.lip})$); `relativePatchDistinctWeights oldPatch` $\le \mathrm{stage} + 1$ (the number of distinct weights).
--   - $f : \mathbb{Z}^{n_X} \to \mathbb{R}$ with $f(x) \in [0, 1]$ for $x \in$ `integerBox N`, such that the set $\{x \in \texttt{integerBox N} : f(x) \ne 0\}$ contains no nontrivial arithmetic progression of length $s + 2$ (`IntegerVectorAPFree`: for all $a$ and all $d \ne 0$ in $\mathbb{Z}^{n_X}$, some $a + i d$ with $0 \le i < s+2$ lies outside the set).
--   - For every $z \in$ `productive`, `AllocatedPathProductivity B U b S N A.widths A.bases (relativePatchSourceTest N f a oldPatch) gain z` holds (OpenAI's predicate: the physical sites of the path are injective in the site and the average of the test over the sites is at least $\mathrm{gain}/2$; the test is `relativePatchSourceTest`, $y \mapsto (\text{box input of } f \text{ at } \lfloor y \rfloor - a)$ times the value of `oldPatch` at $y$).
--
--   **Conclusion.** For every $z \in$ `productive` there is a function `fixed` from $\{k \in \mathrm{Vars} : \neg (H \le \texttt{A.sides}\ k)\}$ to $\mathbb{Z}$ with $0 \le \texttt{fixed}\ k < \texttt{A.sides}\ k$ for all such $k$, such that
--   `RelativePatchSliceConclusion s` $N'$ $g$ $\bigl((1 - \mathrm{discount})^{\mathrm{stage}+1} \Lambda\bigr)$ $(d_0 + sE)$ $(\mathrm{childCost}(p_{\mathrm{child}}))$
--   holds, where $N'$ is `A.sides` restricted to $\{k \in \mathrm{Vars} : H \le \texttt{A.sides}\ k\}$, and $g(u) = f\bigl(\texttt{jointIntegerPhysicalSite}\ w\ (z_1, z_2)\bigr)$ with $w$ the point of $\mathbb{Z}^{\mathrm{Vars}}$ equal to $u$ on the coordinates with $H \le \texttt{A.sides}\ k$ and to `fixed` on the others (`finiteSplitPoint`), and `jointIntegerPhysicalSite root (base, v)` $=$ base $+$ the integer physical site of `root` along $v$ (defined by OpenAI). `RelativePatchSliceConclusion s N g target rankBound cost` is OpenAI's predicate: there exist $q' > 0$, a residue box slice of $N$ with step $q'$ whose side lengths are at least $e^{-\mathrm{cost}} N_i$, and a polynomial patch with at most rankBound slots and complexity at most cost, whose slice score of $g$ relative to target is at least $e^{-\mathrm{cost}}$.
--
--   Lean: `OAI.Erdos3.PolynomialPatch.LowestLayerModel.returned_fibers_of_productive_padded_relative_induction_s2`, which states OpenAI's `OAI.Erdos3.PolynomialPatch.LowestLayerModel.returned_fibers_of_productive_padded_relative_induction` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductivePaddedRelativeInitialization.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B259` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductivePaddedRelativeInitialization.lean (declaration OAI.Erdos3.PolynomialPatch.LowestLayerModel.returned_fibers_of_productive_padded_relative_induction)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B259

section

namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

attribute [local irreducible] integerBox

include hmq in

theorem returned_fibers_of_productive_padded_relative_induction_s2
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride))
    (center : CoefficientTorus (K := Vars) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells center)
    (centerLift : ∀ j, U j)
    (productive : Finset A.Path)
    (sample : productive → CoefficientSamplerArrays (K := Vars) I n)
    (read : productive → AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
        (fun j => (L.pad q j).poly) hm centerLift z.val.1.val z.val.2.val (sample z) (read z))
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hproductive : ∀ z : productive,
      AllocatedPathProductivity B U b S N A.widths A.bases
        (relativePatchSourceTest N f a oldPatch) gain z.val)
 :
    ∀ z ∈ productive, ∃ (fixed : {k : Vars // ¬H ≤ A.sides k} → ℤ),
      (∀ k, 0 ≤ fixed k ∧ fixed k < (A.sides k.val : ℤ)) ∧
      RelativePatchSliceConclusion s (fun k : {k : Vars // H ≤ A.sides k} => A.sides k.val)
        (fun u => f (jointIntegerPhysicalSite
          (finiteSplitPoint (fun k : Vars => H ≤ A.sides k) u fixed) (z.1.val,z.2.val)))
        ((1 - discount) ^ (stage + 1) * Λ) (d₀ + s * E) (childCost pchild) := by
  sorry

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
end
