-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_l1_of_length_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_of_length_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:11:02.133156+00:00
-- url     : https://prove2.me/theorems/79b85100-0feb-4c2a-b825-b48b92d0da7a
-- title:
--   L1 comparison of the whole progression law with the masked covered profile of the averaged sliced ideal, given a large enough length
-- statement:
--   **Setting.** Let $m$ be a natural number and $G$ a finite type with decidable equality. For $j \in \operatorname{Fin} m$ let $I_j$, $J_j$, $Q_j$ be finite types and $n_j$ a natural number; let $B$ assign a finite type with decidable equality to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$, let `euclideanSubspace (U j)` be that subspace in the Euclidean space $\mathbb{R}^{J_j}$ (defined by OpenAI), let `basis j` be a real basis, indexed by $\operatorname{Fin} n_j$, of its orthogonal complement whose integer span equals `projectedIntegerLattice` (the projection of $\mathbb{Z}^{J_j}$ onto that complement; hypothesis hb), let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$, and let $bW_j$ be a $\mathbb{Z}$-basis, indexed by $Q_j$, of `latticeSection` (the lattice $\mathbb{Z}^{J_j} \cap$ `euclideanSubspace (U j)`), each of which is a full lattice. Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$, and let $S$ be a `LayerSamplerScale B U basis R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality and `rowSets j` a finite set of subsets of $\alpha$ for each $j$; write `rows j` for the map sending an element of `rowSets j` to the underlying subset. Let $x : G \to$ `IntegerScalarCubeBox α S.value` (functions $\mathrm{Option}\ \alpha \to [-\texttt{S.value}, \texttt{S.value}) \cap \mathbb{Z}$), and for each $j$ let $s_j$ be an embedding of `rowSets j` into `BoundedIntegerExponent G (j+1)` (exponent vectors on $G$ of total degree at most $j+1$) such that (hA) the square submatrix of `scalarKernelIntegerJet x (j+1) (rows j)` (OpenAI's integer jet matrix of the cube $x$) on the columns $s_j$ has nonzero determinant. Let $M_k > 0$ be a natural number with (hi) `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/Mk)` for all $j$ (OpenAI's predicate bounding the norm of the inverse of the pivot map). Let $P \ge 0$ be real with $M_k \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$, and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$ for all $j$. Let $d \ne 0$ be a natural number.
--
--   Write `grid` for the predicate `allocatedGridAxis U basis S.value` on axes (an integer axis $(j, i)$ is a grid axis when its basis scale is at most $\texttt{S.value}^{\texttt{layerTailDegree } m + 1}$; real axes are not), and `Tuple` for the pairs (non-grid axis $a$, element of $B(a) \times \operatorname{Fin}(\text{degree of } a)$), with $L$ = the principal side lengths `allocatedPrincipalSides B U basis S` on these. Let $H_0, \mathrm{step}_0 : \texttt{PrincipalTupleIndex B (layerSamplerDegree I n)} \to \mathbb{N}$ and $c_0$ with values in $\mathbb{Z}$ with $H_0(t) > 0$ and (hsubset₀) `integerProgressionSupport (c₀ t) (step₀ t) (H₀ t)` (the progression $c_0(t) + \mathrm{step}_0(t) \cdot k$, $0 \le k < H_0(t)$) contained in $[0, \texttt{allocatedPrincipalSides B U basis S t})$ for all $t$. Let `modulus` be a natural number and $r_0$ a residue assignment $t \mapsto (\mathrm{Option}\ \alpha \to \mathbb{Z}/\text{modulus})$ such that (hcell) the cell $\{y : \text{residues of } y \bmod \text{modulus} = r_0\}$ has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀`. Let `wholeLaw` = `containedSupportedProgressionLaw ... H₀ step₀ c₀ ... modulus r₀ hcell` and `gridLaw` = `containedSupportedProgressionAxisLaw ... grid` (OpenAI's finite probability laws on principal integer tuples, respectively on their grid-axis part). Let $\nu_j$ be left-invariant probability measures on the quotient of `euclideanSubspace (U j)` by `latticeSection`, let $\xi$ be the product measure $\prod_j \prod_{\texttt{rowSets } j} \nu_j$, let `CoefficientTorus U` (for the variables `LayerSamplerVariables G I n B`) be compact with a Borel measurable structure and let $\mu$ be a left-invariant probability measure on it. Let `density` = `allocatedCoefficientDensity B U basis hb o hR hσ S` (OpenAI's density on the coefficient torus) and `cover` = multiplication by $d$ on the coefficient torus.
--
--   **Hypotheses.** Let $D, \mathrm{target}, P_k, P_\rho, F, T_{\mathrm{mod}}$ be reals with:
--   - `AllocatedComparisonDimensions B α (rowSets) D` (OpenAI's predicate: $D$ bounds the relevant dimensions); $P_k \ge 0$, $M_k \le e^{P_k}$, $P_\rho \ge 0$, $\mathrm{target} \ge 0$, $F \ge 0$, $T_{\mathrm{mod}} \ge 0$;
--   - (hlength) $\exp(\texttt{allocatedAffineLengthLog m D P Prho Pk target F Tmod}) \le \texttt{S.value}$ (an explicit function of OpenAI);
--   - $g(y, \cdot)$, for each principal integer tuple $y$, a measurable, nonnegative, $\xi$-integrable real function on `EuclideanJetLayers U (rowSets)`, such that (hglaw) for every $y$ the pushforward of the measure with density $z \mapsto \texttt{density}(\texttt{cover}(z))$ with respect to $\mu$ under `euclideanCoefficientJetMap U (root y) (dirs y) rows` equals the measure with density $g(y, \cdot)$ with respect to $\xi$, where root $y$ = `allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y` and dirs $y$ = `allocatedPhysicalCubeDirections B U basis S x y`;
--   - reals $\delta, \eta$, a function $\rho$ from predicates on axes to $\mathbb{R}_{\ge 0}$, and $t \le 1$ with `AllocatedAffineCoveredComparison B rows δ η ρ t htone` (an OpenAI comparison hypothesis, universally quantified over the remaining data); $0 < \rho(\texttt{grid}) \le 1$; $\sigma_j \le t$ for all $j$;
--   - $\mathrm{step}(j) > 0$ for every $j \in$ `Tuple` (where step, $H$, $c$ are $\mathrm{step}_0, H_0, c_0$ restricted to `Tuple`); $\delta > 0$, $\delta^{-1} \le e^F$; (hdense) $\delta L(j) \le |\texttt{integerProgressionSupport}(c(j), \mathrm{step}(j), H(j))|$ for $j \in$ `Tuple`;
--   - $\text{modulus} > 0$ and $\text{modulus} \le e^{T_{\mathrm{mod}}}$;
--   - an embedding `selection` $: \alpha \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x` (OpenAI's predicate: the normalised scalar cube minor exceeds $1/M_k$ in absolute value and the difference lattice has period bounded by $M_k$); $|\alpha| \le m + 1$; every element of `rowSets j` has at most $j+1$ elements; (hperiod) for each $j$, the lattice $\text{modulus} \cdot \mathbb{Z}^{\texttt{rowSets } j}$ is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)`;
--   - $v_0$, a tuple on the non-grid axes, with nonzero weight under the law `containedProgressionResidueLaw` built from the active data $L, H, \mathrm{step}, c$, modulus and residues $r_0$ (with the admissibility proof provided by OpenAI's lemma `allocatedAffineLength_slice_ready`);
--   - $T : \operatorname{Fin} m \to \mathbb{R}$ with $T_j \ge$ `partitionedIdealRadius α m` $+ 1$ (where `partitionedIdealRadius α m` $= 1/4 + 2^{|\alpha|} (|\alpha| + 1)^m$) and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \cdot 2^{|\alpha|} (|\alpha| + 1)^{j+1} \le T_j$;
--   - $C : \operatorname{Fin} m \to \mathbb{R}$ with $C_j \ge 0$, $\lVert \Phi_j^{-1}(v) \rVert \le C_j \lVert v \rVert$ for all $v$, where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)`, and $C_j (|I_j| + 1) T_j R_j \le 1/4$;
--   - $\rho(\texttt{grid})^{-1} \le e^{P_\rho}$; $0 \le \eta \le \exp\bigl(-(\mathrm{target} + 1 + D \cdot m\, 2^{m+1} P_k + 4)\bigr)$.
--
--   **Conclusion.** Let `center` = `principalProgressionSliceCenter activeB activeDegree L c` and `width` = `principalProgressionSliceWidth activeB activeDegree L H step` (OpenAI's slice center and width on the non-grid axes), and let `ideal` = `diagonalImageDensity` $(o \mapsto R_{j(o)})$ applied to `activeAveragedSlicedProfileIdeal (G × Option α) (layerSamplerDegree I n) grid rows (ρ grid) center width` (OpenAI's averaged sliced profile, rescaled coordinatewise by the $R_j$: `diagonalImageDensity d f x` $= (\prod_i |d_i|)^{-1} f(x/d)$). Then
--   $$\int \Bigl| \mathbb{E}_{v \sim \texttt{wholeLaw}}\, g(v, y) - \mathbb{E}_{u \sim \texttt{gridLaw}}\, \texttt{allocatedWholeMaskedCoveredProfile B U basis hR hsigma S x rows hb o bW d (principalAxisJoin grid u v0) modulus ideal}(y) \Bigr| \, d\xi(y) \le e^{-\mathrm{target}},$$
--   where `principalAxisJoin grid u v₀` is the tuple equal to $u$ on grid axes and $v_0$ on the others, and `allocatedWholeMaskedCoveredProfile` is OpenAI's masked covered profile density. (The Lean statement also introduces an unused local definition `_outputResidue`.)
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_of_length_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_of_length` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRecenteredSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B235` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRecenteredSource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_of_length)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B235

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, ↥(rowSets j) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowSets j → Finset α)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := ↥(rowSets j))
  S.positive x (j.val + 1) (Subtype.val : rowSets j → Finset α) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ j, Nonempty (rowSets j)] in
theorem allocatedAffineIdeal_l1_of_length_s2
    {D target Pk Prho F Tmod : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B α selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hTmod : 0 ≤ Tmod)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) ξ)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure ξ (g y))
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hmodulus : (modulus : ℝ) ≤ Real.exp Tmod)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    (hrowDegree : ∀ j (a : rowSets j), a.val.card ≤ j.val + 1)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue (allocatedAffineLength_slice_ready B U basis hdimensions hP hPrho hPk htarget hF hTmod S hlength H₀ step₀ c₀ hsubset₀ hδ hδF modulus hm hmodulus hstep hdense).2.1).weight v₀ ≠ 0)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let _outputResidue := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    (∫ y, ‖((wholeLaw).mean (fun v => g v y) : ℂ) -
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ)‖ ∂ξ) ≤
      Real.exp (-target) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
