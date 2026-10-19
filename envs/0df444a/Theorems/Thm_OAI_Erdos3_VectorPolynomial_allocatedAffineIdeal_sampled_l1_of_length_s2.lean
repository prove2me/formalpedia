-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_sampled_l1_of_length_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_sampled_l1_of_length_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:00:11.096352+00:00
-- url     : https://prove2.me/theorems/112fc9d3-8972-4a7e-9859-47d487db6d9e
-- title:
--   Sampled L1 comparison between the whole-law mean and the masked covered profile along physical cube row samples
-- statement:
--   **Setup.** Fix the data of OpenAI's allocated layer-sampler setup: natural numbers $m$, $\mathrm{dim}$, $M_k$, $d$ with $M_k > 0$ and $d \ne 0$; finite types $G$ (with decidable equality), $I_j$, $J_j$, $Q_j$ ($j < m$), $B(a)$ for each layer-sampler axis $a$ (finite, with decidable equality), and $X$ (finite, with decidable equality); dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases `basis j` (indexed by $\{0,\dots,n_j-1\}$) of the orthogonal complement of $U_j$, with $hb$: the $\mathbb{Z}$-span of `basis j` equals `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ (indexed by $I_j$) of $U_j$; $\mathbb{Z}$-bases $bW_j$ (indexed by $Q_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (assumed to be a $\mathbb{Z}$-lattice); reals $R_j > 0$, $\sigma_j > 0$; a `LayerSamplerScale B U basis R σ` $S$ (with integer side `S.value`); finite sets `rowSets j` of subsets of $\{0,\dots,\mathrm{dim}-1\}$, with selected rows $\texttt{selectedRows}\ j = $ `rowSets j` viewed as a type and $\texttt{rows}\ j$ the inclusion; a point $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`; embeddings $s_j$ of `rowSets j` into `BoundedIntegerExponent G (j+1)` such that ($hA$) the square submatrix of `scalarKernelIntegerJet x (j+1) rows` selected by $s_j$ has nonzero determinant for each $j$, and ($hi$) `fixedKernelInverseBound S.positive x (j+1) rows (s j) (hA j) (1/Mk)` holds for each $j$; a real $P \ge 0$ with $M_k \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ and $\lvert$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`$\rvert + 1 \le e^P$ for every $j$; functions $H_0, \mathrm{step}_0 : $ `PrincipalTupleIndex B (layerSamplerDegree I n)` $\to \mathbb{N}$ and $c_0$ to $\mathbb{Z}$ with $H_0(t) > 0$ and ($hsubset_0$) the progression `integerProgressionSupport (c₀ t) (step₀ t) (H₀ t)` contained in $[0, \texttt{allocatedPrincipalSides B U basis S}\ t)$ for every $t$; a natural number `modulus` and residues $r_0(t, \cdot) : $ `Option (Fin dim)` $\to \mathbb{Z}/\mathrm{modulus}$, with ($hcell$) positive mass of the residue cell $\{y : \texttt{principalResidueLabel modulus}\ y = r_0\}$ under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀`; probability measures $\nu_j$ (left-invariant) on the tori $U_j / \texttt{latticeSection}$, and left-invariant probability measures $\mu$ on `CoefficientTorus (K := LayerSamplerVariables G I n B) U` and $\mu_{\mathrm{rows}}$ on `CoefficientTorus (K := Fin dim) U` (both compact Borel spaces). (The measure $\mu_{\mathrm{rows}}$ and the hypotheses on $R, \sigma, M_k, P$ listed above are included in the statement even where they do not appear in the conclusion.)
--
--   Notation: `grid` $=$ `allocatedGridAxis U basis S.value` (a predicate on axes); the active axes are those not in `grid`; $\mathrm{Tuple}$ is the principal tuple index for the active axes, $L$ = `principalAxisLength (¬grid) (allocatedPrincipalSides B U basis S)`, and $H, \mathrm{step}, c, \mathrm{residue}$ are the restrictions of $H_0, \mathrm{step}_0, c_0, r_0$ to $\mathrm{Tuple}$. `wholeLaw` and `gridLaw` are the OpenAI probability laws `containedSupportedProgressionLaw …` and `containedSupportedProgressionAxisLaw … grid` built from these data; $\xi = \prod_j \prod_{\texttt{rowSets}\ j} \nu_j$; `density` $=$ `allocatedCoefficientDensity B U basis hb o hR hσ S` and `cover` $=$ `quotientIntegerCover (coefficientIntegerLattice U) d`; `wholeRoot y` and `wholeDirs y` are `allocatedPhysicalCubeRoot B U basis S 0 x y` and `allocatedPhysicalCubeDirections B U basis S x y`.
--
--   **Hypotheses.** Let $D, \mathrm{target}, P_k, P_\rho, F, T_{\mathrm{mod}}, \delta, \eta, t$ be reals and assume:
--   - `AllocatedComparisonDimensions B (Fin dim) selectedRows D` (OpenAI: $D \ge 0$ bounds $m$, $\lvert G\rvert$, $\mathrm{dim}$, the number of axes, tuples, and similar counts);
--   - $P_k \ge 0$, $M_k \le e^{P_k}$, $P_\rho \ge 0$, $\mathrm{target} \ge 0$, $F \ge 0$, $T_{\mathrm{mod}} \ge 0$;
--   - $\exp(\texttt{allocatedAffineLengthLog}\ m\ D\ P\ P_\rho\ P_k\ \mathrm{target}\ F\ T_{\mathrm{mod}}) \le \texttt{S.value}$ (an explicit OpenAI length budget);
--   - $g(y, \cdot)$, for each principal integer tuple $y$, is a measurable, nonnegative, $\xi$-integrable real function on `EuclideanJetLayers U selectedRows`, and for each $y$ the push-forward of the measure with density $z \mapsto \texttt{density}(\texttt{cover}(z))$ with respect to $\mu$ under `euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows` equals the measure with density $g(y, \cdot)$ with respect to $\xi$;
--   - $\rho$ is a map from predicates on axes to $\mathbb{R}_{\ge 0}$, $t \le 1$, and `AllocatedAffineCoveredComparison B rows δ η ρ t htone` holds (an OpenAI-defined comparison property); $0 < \rho(\texttt{grid}) \le 1$; $\sigma_j \le t$ for all $j$;
--   - $\mathrm{step}(j) > 0$ for all $j \in \mathrm{Tuple}$; $\delta > 0$ and $\delta^{-1} \le e^F$; $\delta L(j) \le$ the size of `integerProgressionSupport (c j) (step j) (H j)` for all $j \in \mathrm{Tuple}$;
--   - $0 < \mathrm{modulus} \le e^{T_{\mathrm{mod}}}$;
--   - `selection` is an embedding of $\{0,\dots,\mathrm{dim}-1\}$ into $G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x`; $\mathrm{dim} \le m+1$; every row set in `rowSets j` has at most $j+1$ elements; and for every $j$ the lattice `integerScalarLattice (selectedRows j) modulus` is contained in the range of the matrix `scalarKernelIntegerJet x (j+1) (rows j)`;
--   - $v_0$ is a tuple in `PrincipalAxisTuples (¬grid) (allocatedPrincipalSides B U basis S)` whose weight under the contained progression residue law `containedProgressionResidueLaw …` (formed for the active axes from $L, H, \mathrm{step}, c, \mathrm{modulus}, \mathrm{residue}$) is nonzero;
--   - $T_j$ are reals with $\texttt{partitionedIdealRadius (Fin dim) m} + 1 \le T_j$ and $\lvert\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}\rvert \cdot 2^{\mathrm{dim}} (\mathrm{dim}+1)^{j+1} \le T_j$;
--   - $C_j \ge 0$ are reals with $\lVert \texttt{normalizedOrthogonalChart}(U_j, \texttt{basis}\ j)^{-1}(v)\rVert \le C_j\lVert v\rVert$ for all $v$, and $C_j (\lvert I_j\rvert + 1) T_j R_j \le 1/4$;
--   - $\rho(\texttt{grid})^{-1} \le e^{P_\rho}$; $0 \le \eta \le \exp(-(\mathrm{target} + 1 + D \cdot (m\, 2^{m+1}) P_k + 4))$.
--
--   **Conclusion.** Let $\mathrm{center}$ and $\mathrm{width}$ be `principalProgressionSliceCenter activeB activeDegree L c` and `principalProgressionSliceWidth activeB activeDegree L H step`; let `ideal` be `diagonalImageDensity` (with scales $R_{j}$ on the active row coordinates) of `activeAveragedSlicedProfileIdeal (G × Option (Fin dim)) (layerSamplerDegree I n) grid rows (ρ grid) center width`; let $\mathrm{profile}(y)$ be the complex number given by the `gridLaw`-mean over $u$ of `allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows hb o bW d (principalAxisJoin grid u v₀) modulus ideal y`; and let $A$ be the natural number chosen (by `Classical.choose`) from OpenAI's theorem `exists_translated_physical_jet_l1_perturbation m dim`. Then for all reals $P_{\mathrm{sample}}, R_{\mathrm{rank}}, S_{\mathrm{stride}}, \tau, \varepsilon_{\mathrm{sample}}, \eta_{\mathrm{sample}}, \delta_{\mathrm{sur}}$ the following holds. Suppose $0 \le P_{\mathrm{sample}}$, $\lvert X\rvert \le P_{\mathrm{sample}}$, $\lvert \texttt{Option (Fin dim)} \times X\rvert \le P_{\mathrm{sample}}$; let $\mathrm{base} : X \to \mathbb{Z}$, and for each $j$ let $\mathrm{poly}_j$ be a `VectorPolynomial X ℝ (J j → ℝ)` of degree at most $j+1$ (with unit weights) all of whose coefficients lie in $U_j$; suppose $d \le e^{P_{\mathrm{sample}}}$; let $\mathrm{stride} : X \to \mathbb{N}$ be positive with $\mathrm{stride}(i) \le S_{\mathrm{stride}}$, $0 \le S_{\mathrm{stride}} \le e^{P_{\mathrm{sample}}}$, $\tau > 0$, $\varepsilon_{\mathrm{sample}} > 0$, $1/\tau \le e^{P_{\mathrm{sample}}}$, $1/\varepsilon_{\mathrm{sample}} \le e^{P_{\mathrm{sample}}}$; let $N : X \to \mathbb{R}$ with $e^{(P_{\mathrm{sample}} + A)^A} \le N(i)$ for all $i$, with `HasLayerSamplingRank (j+1) N Rrank (U j) (poly j)` for all $j$ and $e^{(P_{\mathrm{sample}} + A)^A} \le R_{\mathrm{rank}}$; let `cells` be a nonempty finite set of `ColumnResiduePattern (Option (Fin dim)) X stride`; let $V : \texttt{Option (Fin dim)} \times X \to \mathbb{R}$ with $V(z) > 0$ and $\tau N(z_2) \le V(z)$; let `actual` and `surrogate` be complex functions on `JetAmbientIndex selectedRows J → UnitAddCircle` that are Lipschitz with constants $L_a, L_s \in \mathbb{R}_{\ge 0}$ and bounded in norm by $C_a, C_s \in \mathbb{R}_{\ge 0}$; suppose $\eta_{\mathrm{sample}} > 0$, $\lvert\texttt{CoefficientAmbientIndex (Fin dim) J}\rvert \le P_{\mathrm{sample}}$, $L_a, L_s, C_a, C_s \le e^{P_{\mathrm{sample}}}$, $\sum_{j<m} \lvert\texttt{BoundedCoefficientExponent (Fin dim) (j+1)}\rvert \le e^{P_{\mathrm{sample}}}$, $\eta_{\mathrm{sample}}^{-1} \le e^{P_{\mathrm{sample}}}$; suppose that for every $y$ the `wholeLaw`-mean of $v \mapsto g(v, y)$ (as a complex number) equals $\mathrm{actual}(\texttt{coveredJetAmbientTorus U 1 y})$, and $\lVert \mathrm{profile}(y) - \mathrm{surrogate}(\texttt{coveredJetAmbientTorus U 1 y})\rVert \le \delta_{\mathrm{sur}}$ for every $y$. Then the total weight $\sum_z \texttt{selectedResidueSmoothWeight stride cells V}\ z$ is positive, and
--   $$\texttt{selectedResidueDensityMass stride cells V}\Bigl(z \mapsto \bigl\lVert \mathbb{E}_{\mathrm{wholeLaw}}[v \mapsto g(v, \mathrm{point}_z)] - \mathrm{profile}(\mathrm{point}_z)\bigr\rVert\Bigr) \le e^{-\mathrm{target}} + 2\delta_{\mathrm{sur}} + (2\eta_{\mathrm{sample}} + \varepsilon_{\mathrm{sample}}),$$
--   where $\mathrm{point}_z = $ `physicalCubeRowSample U d rows poly hmem (translatePhysicalCube base (standardPhysicalCubeOutput z))` and `selectedResidueDensityMass` is OpenAI's normalized mass with respect to the smooth weights `selectedResidueSmoothWeight` (a smooth product profile in $z/V$, restricted to $z$ whose column residue pattern modulo `stride` lies in `cells`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_sampled_l1_of_length_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_sampled_l1_of_length` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRecenteredSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B235` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRecenteredSource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_sampled_l1_of_length)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B235

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ uX
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {dim : ℕ}
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (s : ∀ j : Fin m, ↥(rowSets j) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowSets j → Finset (Fin dim))).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := ↥(rowSets j))
  S.positive x (j.val + 1) (Subtype.val : rowSets j → Finset (Fin dim)) (s j) (hA j) (1 / (Mk : ℝ)))
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
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
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

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin dim) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

include μrows hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ j, Nonempty (rowSets j)] in
theorem allocatedAffineIdeal_sampled_l1_of_length_s2
    {D target Pk Prho F Tmod : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hTmod : 0 ≤ Tmod)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S) →
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
    (selection : (Fin dim) ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card (Fin dim) ≤ m + 1)
    (hrowDegree : ∀ j (a : rowSets j), a.val.card ≤ j.val + 1)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := (Fin dim)) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue (allocatedAffineLength_slice_ready B U basis hdimensions hP hPrho hPk htarget hF hTmod S hlength H₀ step₀ c₀ hsubset₀ hδ hδF modulus hm hmodulus hstep hdense).2.1).weight v₀ ≠ 0)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))) :
    let center := principalProgressionSliceCenter (α := (Fin dim)) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := (Fin dim)) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option (Fin dim))
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let profile := fun y => ((gridLaw).mean (fun u =>
      allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ)
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,0} m dim)
    ∀ {Psample Rrank Sstride τ εsample ηsample δsur : ℝ},
    0 ≤ Psample → (Fintype.card X : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Psample →
    ∀ (base : X → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j),
    (d : ℝ) ≤ Real.exp Psample →
    ∀ (stride : X → ℕ), (∀ i, 0 < stride i) →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < τ → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    ∀ (N : X → ℝ), (∀ i, Real.exp ((Psample + A) ^ A) ≤ N i) →
    (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    ∀ (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)), cells.Nonempty →
    ∀ (V : Option (Fin dim) × X → ℝ), (∀ z, 0 < V z) → (∀ z, τ * N z.2 ≤ V z) →
    ∀ (actual surrogate : (JetAmbientIndex selectedRows J → UnitAddCircle) → ℂ)
      (La Ls Ca Cs : ℝ≥0),
    LipschitzWith La actual → LipschitzWith Ls surrogate →
    (∀ z, ‖actual z‖ ≤ Ca) → (∀ z, ‖surrogate z‖ ≤ Cs) →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Psample →
    (La : ℝ) ≤ Real.exp Psample → (Ls : ℝ) ≤ Real.exp Psample →
    (Ca : ℝ) ≤ Real.exp Psample → (Cs : ℝ) ≤ Real.exp Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    (∀ y, ((wholeLaw).mean (fun v => g v y) : ℂ) = actual (coveredJetAmbientTorus U 1 y)) →
    (∀ y, ‖profile y - surrogate (coveredJetAmbientTorus U 1 y)‖ ≤ δsur) →
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      selectedResidueDensityMass stride cells V (fun z =>
        let point := physicalCubeRowSample U d rows poly hmem
          (translatePhysicalCube base (standardPhysicalCubeOutput z))
        ‖((wholeLaw).mean (fun v => g v point) : ℂ) - profile point‖) ≤
          Real.exp (-target) + 2 * δsur + (2 * ηsample + εsample) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
