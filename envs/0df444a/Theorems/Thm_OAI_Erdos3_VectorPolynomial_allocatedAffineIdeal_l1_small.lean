-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_l1_small
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_small
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T01:07:18.436346+00:00
-- url     : https://prove2.me/theorems/46d7ee3b-bbbd-4d55-b5cc-dab5d6a98076
-- title:
--   Under small-parameter bounds the affine ideal L1 error is at most exp(-target)
-- statement:
--   Fix the section data. A natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$, natural numbers $n_j$, finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$ (in a universe $u_J$), real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, $W_j = \mathbb Z^{J_j} \cap V_j$ (`latticeSection`), bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L_S = $ `S.value`; a finite type $\alpha$ with decidable equality; for each $j$ a finite family $\mathrm{rowSets}_j$ of subsets of $\alpha$, with row types $\mathrm{selectedRows}_j = \{t : t \in \mathrm{rowSets}_j\}$ and $\mathrm{rows}_j$ the inclusion $\mathrm{selectedRows}_j \to \mathrm{Finset}\,\alpha$; a point $x : G \to $ `IntegerScalarCubeBox α L_S`; embeddings $s_j : \mathrm{selectedRows}_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` with the column-restricted matrices of `scalarKernelIntegerJet x (j+1) (rows j)` nonsingular ($hA$); a positive natural number $M_k$ with `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/Mk)` for all $j$; a real $P \ge 0$ with $M_k \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$; finite types $Q_j$ (in a universe $u_Q$); the hypothesis $hb$ that the $\mathbb Z$-span of `basis j` is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $W_j$ indexed by $Q_j$; a positive natural number $d$; natural-valued $H_0, \mathrm{step}_0$ and integer-valued $c_0$ on `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H_0 > 0$ and each progression $\{c_0(t) + \mathrm{step}_0(t)k : 0 \le k < H_0(t)\}$ contained in $[0, \texttt{allocatedPrincipalSides B U basis S t})$; a natural number $\mathrm{modulus}$ and residues $r_0(t,i) \in \mathbb Z/\mathrm{modulus}$ with $hcell$: the tuples with residue label $r_0$ have positive mass under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀`; the assumption that each $W_j$ is a full lattice in $V_j$; additively left-invariant probability measures $\nu_j$ on $V_j/W_j$; and a compact Borel structure on `CoefficientTorus U` with an additively left-invariant probability measure $\mu$ on it.
--
--   Notation: grid is the predicate `allocatedGridAxis U basis L_S`; Tuple is the principal tuple index over non-grid axes; $L = $ `principalAxisLength (¬ grid) (allocatedPrincipalSides B U basis S)`; $H, \mathrm{step}, c, \mathrm{residue}$ are the restrictions of $H_0, \mathrm{step}_0, c_0, r_0$ to Tuple; wholeLaw is `containedSupportedProgressionLaw … H₀ step₀ c₀ … modulus r₀ hcell` and gridLaw is `containedSupportedProgressionAxisLaw … grid` (finite probability weights defined by OpenAI on all integer tuples, resp. on `PrincipalAxisTuples grid (allocatedPrincipalSides B U basis S)`); $\xi = \prod_j \prod_{\mathrm{rowSets}_j} \nu_j$; $\mathrm{density} = $ `allocatedCoefficientDensity B U basis hb o hR hσ S`, a real function on `CoefficientTorus U`; cover is multiplication by $d$ on `CoefficientTorus U` (`quotientIntegerCover`).
--
--   Let $g$ assign to each tuple $y$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S)` a function $g_y : $ `EuclideanJetLayers U selectedRows` $\to \mathbb R$ that is measurable, nonnegative and $\xi$-integrable, such that the push-forward of $\mu$ with density $\mathrm{density} \circ \mathrm{cover}$ under `euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) (allocatedPhysicalCubeDirections B U basis S x y) rows` equals $\xi$ with density $g_y$. Let $\delta, \eta$ be reals, $\rho$ a function from predicates on axes to $\mathbb R_{\ge 0}$, $t \le 1$, and assume: `AllocatedAffineCoveredComparison B rows δ η ρ t htone`; $0 < \rho(\mathrm{grid}) \le 1$; $\sigma_j \le t$; for $j \in$ Tuple, $\mathrm{step}_j > 0$, $H_j \ge 2$, $\delta L_j \le |\{c_j + \mathrm{step}_j k : 0 \le k < H_j\}|$, $(|\alpha|+1)\,\mathrm{modulus} \le H_j$, `scalarCubeGridBoundaryConstant α` $\cdot\,\mathrm{modulus}/H_j <$ the Lebesgue measure of `scalarCubeDomain α`, and $\mathrm{step}_j/L_j \le \varepsilon$ for a real $\varepsilon \ge 0$; $\delta > 0$; $\mathrm{modulus} > 0$; an embedding $\mathrm{selection} : \alpha \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x`; $|\alpha| \le m+1$; $|t| \le j+1$ for every row $t \in \mathrm{rowSets}_j$; reals $e \ge 0$, $\varepsilon_{\mathrm{coef}} > 0$ with $\varepsilon_{\mathrm{coef}}^{-1} \le \exp(e)$; $\exp(\texttt{allocatedKernelReplacementLog B α selectedRows P e}) \le L_S$; $\mathrm{modulus}\cdot\mathbb Z^{\mathrm{selectedRows}_j}$ is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)` for every $j$; a non-grid tuple $v_0$ of nonzero weight under `containedProgressionResidueLaw … L H step c … modulus hm residue hsize`; a real $\mathrm{mesh} \in [0,1]$ with $1/L_S^{\,\texttt{layerTailDegree}\ m+1} \le \mathrm{mesh}$; $T : \mathrm{Fin}\,m \to \mathbb R$ with `partitionedIdealRadius α m` $+1 \le T_j$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}|\cdot 2^{|\alpha|}(|\alpha|+1)^{j+1} \le T_j$; $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ (\texttt{basis}\ j))^{-1}v\| \le C_j\|v\|$ and $C_j(|I_j|+1)T_jR_j \le 1/4$; and reals $D, \mathrm{target}, P_k, P_\rho$ with `AllocatedComparisonDimensions B α selectedRows D`, $P_k \ge 0$, $M_k \le e^{P_k}$, $P_\rho \ge 0$, $\rho(\mathrm{grid})^{-1} \le e^{P_\rho}$, $\mathrm{target} \ge 0$, $\eta \ge 0$, and, writing $\Lambda = $ `allocatedAffineL1Log m D P Prho Pk`,
--   $\varepsilon_{\mathrm{coef}} \le \exp(-(\mathrm{target} + 1 + \texttt{coefficientReplacementErrorLog}\ D\ \Lambda))$ (where `coefficientReplacementErrorLog D Λ` $= 3(D+1)(\Lambda+3)$), $\eta \le \exp(-(\mathrm{target} + 1 + D\,m\,2^{m+1}P_k + 4))$, and each of $\sum_{j \in \mathrm{Tuple}} \mathrm{modulus}/H_j$, $\varepsilon$ and $\mathrm{mesh}$ is at most $\exp(-(\mathrm{target} + 1 + \texttt{affineReferenceCoefficientLog}\ D\ \Lambda + 4))$ (where `affineReferenceCoefficientLog D Λ` $= 8(D+1)(\Lambda+1)$).
--
--   Let ideal be `diagonalImageDensity (o ↦ R_{layer(o)}) (activeAveragedSlicedProfileIdeal (G × Option α) (layerSamplerDegree I n) grid rows (ρ grid) center width)` with center and width given by `principalProgressionSliceCenter … L c` and `principalProgressionSliceWidth … L H step`. Then
--   $$\int \Bigl| \sum_v \mathrm{wholeLaw}(v)\, g_v(y) - \sum_u \mathrm{gridLaw}(u)\, \Phi_u(y) \Bigr|\, d\xi(y) \le e^{-\mathrm{target}},$$
--   where $\Phi_u = $ `allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows hb o bW d (principalAxisJoin grid u v₀) modulus ideal`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_small` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRecenteredSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B129`, `OAIErdos3B136`, `OAIErdos3B143` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRecenteredSource.lean#L211

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B129
import Definitions.Def_OAIErdos3B136
import Definitions.Def_OAIErdos3B143

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
local notation "jetRows" => selectedRows
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

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
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
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

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
theorem allocatedAffineIdeal_l1_small
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
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    (hrowDegree : ∀ j (a : rowSets j), a.val.card ≤ j.val + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    {D target Pk Prho : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B α selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (htarget : 0 ≤ target)
    (hη0 : 0 ≤ η)
    (hcoefsmall : εcoef ≤ Real.exp (-(target + 1 + coefficientReplacementErrorLog D (allocatedAffineL1Log m D P Prho Pk))))
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (hratiosmall : (∑ j : Tuple, (modulus : ℝ) / H j) ≤
      Real.exp (-(target + 1 + affineReferenceCoefficientLog D (allocatedAffineL1Log m D P Prho Pk) + 4)))
    (hεsmall : ε ≤ Real.exp (-(target + 1 + affineReferenceCoefficientLog D (allocatedAffineL1Log m D P Prho Pk) + 4)))
    (hmeshsmall : mesh ≤ Real.exp (-(target + 1 + affineReferenceCoefficientLog D (allocatedAffineL1Log m D P Prho Pk) + 4))) :
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
