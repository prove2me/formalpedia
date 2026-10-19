-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineWholeProfile_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineWholeProfile_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:42:42.234211+00:00
-- url     : https://prove2.me/theorems/19069fb2-50b8-4ada-bebb-cd1cefc5b827
-- title:
--   The allocated progression covered expectation is close to the integral of the grid-averaged whole masked covered profile
-- statement:
--   **Setup.** Fix the data of OpenAI's allocated layer-sampler setup: natural numbers $m$, $M_k > 0$, $d \ne 0$; finite types $G$ (with decidable equality), $I_j$, $J_j$, $Q_j$ ($j < m$), $B(a)$ for each layer-sampler axis $a$ (finite, with decidable equality), $\alpha$ (finite, with decidable equality) and $O_j$ (finite, with decidable equality); dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases `basis j` (indexed by $\{0,\dots,n_j-1\}$) of the orthogonal complement of $U_j$, with $hb$: the $\mathbb{Z}$-span of `basis j` equals `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ (indexed by $I_j$) of $U_j$; $\mathbb{Z}$-bases $bW_j$ (indexed by $Q_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (assumed to be a $\mathbb{Z}$-lattice); reals $R_j > 0$, $\sigma_j > 0$; a `LayerSamplerScale B U basis R σ` $S$ (with integer side `S.value`); row maps $\mathrm{rows}_j : O_j \to$ finite subsets of $\alpha$; a point $x : G \to$ `IntegerScalarCubeBox α S.value`; embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` such that ($hA$) the square submatrix of `scalarKernelIntegerJet x (j+1) (rows j)` selected by $s_j$ has nonzero determinant, and ($hi$) `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/Mk)` holds, for each $j$; a real $P \ge 0$ with $M_k \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ and $\lvert$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`$\rvert + 1 \le e^P$ for every $j$; a measurable function $F$ from `EuclideanJetLayers U O` to $\mathbb{C}$ with $\lVert F\rVert \le 1$ everywhere; functions $H_0, \mathrm{step}_0 :$ `PrincipalTupleIndex B (layerSamplerDegree I n)` $\to \mathbb{N}$ and $c_0$ to $\mathbb{Z}$ with $H_0(t) > 0$ and ($hsubset_0$) `integerProgressionSupport (c₀ t) (step₀ t) (H₀ t)` contained in $[0, \texttt{allocatedPrincipalSides B U basis S}\ t)$ for every $t$; a natural number `modulus` and residues $r_0(t,\cdot) :$ `Option α` $\to \mathbb{Z}/\mathrm{modulus}$ with ($hcell$) positive mass of the cell $\{y : \texttt{principalResidueLabel modulus}\ y = r_0\}$ under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀`; and left-invariant probability measures $\nu_j$ on the tori $U_j/\texttt{latticeSection}$. (The hypotheses on $R, \sigma, M_k, P$ listed above are included in the statement.)
--
--   Notation: `grid` $=$ `allocatedGridAxis U basis S.value`; $\mathrm{Tuple}$ is the principal tuple index of the active (non-grid) axes; $L = $ `principalAxisLength (¬grid) (allocatedPrincipalSides B U basis S)`; $H, \mathrm{step}, c, \mathrm{residue}$ are the restrictions of $H_0, \mathrm{step}_0, c_0, r_0$ to $\mathrm{Tuple}$; `gridLaw` is the OpenAI probability law `containedSupportedProgressionAxisLaw … grid` on grid tuples built from the data above; and `actual` is the complex number `allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d (p ↦ F p.2) H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell` (defined by OpenAI).
--
--   **Hypotheses.** Let $\delta, \eta, t, \varepsilon, e, \varepsilon_{\mathrm{coef}}, \mathrm{mesh}, C_{\mathrm{mask}}$ be reals and assume:
--   - $\rho$ maps predicates on axes to $\mathbb{R}_{\ge 0}$, $t \le 1$, `AllocatedAffineCoveredComparison B rows δ η ρ t htone` holds (an OpenAI-defined property), $0 < \rho(\texttt{grid}) \le 1$, and $\sigma_j \le t$ for all $j$;
--   - for every $j \in \mathrm{Tuple}$: $\mathrm{step}(j) > 0$, $H(j) \ge 2$, $\delta L(j) \le \lvert \texttt{integerProgressionSupport (c j) (step j) (H j)}\rvert$, $(\lvert\alpha\rvert + 1)\cdot \mathrm{modulus} \le H(j)$, $\texttt{scalarCubeGridBoundaryConstant}\ \alpha \cdot \mathrm{modulus}/H(j) < $ the Lebesgue volume of `scalarCubeDomain α`, and $\mathrm{step}(j)/L(j) \le \varepsilon$; and $\delta > 0$, $\mathrm{modulus} > 0$, $\varepsilon \ge 0$;
--   - `selection` is an embedding $\alpha \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x`, and $\lvert\alpha\rvert \le m+1$;
--   - $e \ge 0$, $\varepsilon_{\mathrm{coef}} > 0$, $\varepsilon_{\mathrm{coef}}^{-1} \le e^{e}$, and $\exp(\texttt{allocatedKernelReplacementLog B alpha O P e}) \le \texttt{S.value}$;
--   - for every $j$, `integerScalarLattice (O j) modulus` is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)`;
--   - $v_0$ is an active-axis tuple in `PrincipalAxisTuples (¬grid) (allocatedPrincipalSides B U basis S)` whose weight under `containedProgressionResidueLaw` (formed for the active axes from $L, H, \mathrm{step}, c, \mathrm{modulus}, \mathrm{residue}$ and the size hypothesis above) is nonzero;
--   - $0 \le \mathrm{mesh} \le 1$, $1/\texttt{S.value}^{\,\texttt{layerTailDegree}\ m + 1} \le \mathrm{mesh}$, $1 \le C_{\mathrm{mask}}$, and for every grid tuple $u$, every $j$ and every $z$, $0 \le \texttt{allocatedIntegerKernelMask B U basis S x rows j modulus}(M_{u,j}, z) \le C_{\mathrm{mask}}$, where $M_{u,j} = $ `integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus`;
--   - $T_j$ are reals with `partitionedIdealRadius α m` $+ 1 \le T_j$ and $\lvert\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}\rvert \cdot 2^{\lvert\alpha\rvert}(\lvert\alpha\rvert+1)^{j+1} \le T_j$;
--   - $C_j \ge 0$ are reals with $\lVert\texttt{normalizedOrthogonalChart}(U_j, \texttt{basis}\ j)^{-1}(v)\rVert \le C_j \lVert v\rVert$ for all $v$ and $C_j(\lvert I_j\rvert + 1) T_j R_j \le 1/4$.
--
--   **Conclusion.** Let $\mathrm{center}$ = `principalProgressionSliceCenter activeB activeDegree L c`, $\mathrm{width}$ = `principalProgressionSliceWidth activeB activeDegree L H step`, and `ideal` = `diagonalImageDensity` (with scale $R_j$ on each active row coordinate) of `activeAveragedSlicedProfileIdeal (G × Option α) (layerSamplerDegree I n) grid rows (ρ grid) center width`. Then
--   $$\Bigl\lVert \mathrm{actual} - \int \mathbb{E}_{u \sim \mathrm{gridLaw}}\bigl[\texttt{allocatedWholeMaskedCoveredProfile B U basis hR hsigma S x rows hb o bW d (principalAxisJoin grid u v0) modulus ideal}\ y\bigr]\, F(y)\, d\Bigl(\prod_j \prod_{O_j} \nu_j\Bigr)(y) \Bigr\rVert$$
--   is at most
--   $$\bigl(2e^{\texttt{allocatedJetSupportLog B alpha O P}} + 1\bigr)^{K} \cdot \Bigl(A_{\mathrm{act}}\, \varepsilon_{\mathrm{coef}} \bigl(1 + \texttt{layerKernelIndexBound}(m, M_k)\, e^{\texttt{allocatedDensityLog B alpha O P}} + \varepsilon_{\mathrm{coef}}\bigr)^{A_{\mathrm{act}}}\Bigr) + \texttt{allocatedAffineSourceReferenceError B U basis S alpha O (rho grid) P eta (\_ => modulus) H epsilon mesh Cmask},$$
--   where $K = \lvert \Sigma_{a} O_{a.1}\rvert$ (pairs of a layer-sampler axis $a$ and an element of $O$ at its layer), $A_{\mathrm{act}}$ is the number of active (non-grid) axes, and all named quantities are explicit functions defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineWholeProfile_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineWholeProfile_comparison` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B213`, `OAIE3v2B217` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineWholeProfile_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213
import Definitions.Def_OAIE3v2B217

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
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => O
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
variable (F : EuclideanJetLayers U O → ℂ)

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
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "actual" => allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d (fun p => F (Prod.snd p))
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineWholeProfile_comparison_s2
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
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, O a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let _ := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    ‖actual - (∫ y, ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile
      B U basis hR hσ S x rows hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α O (ρ grid) P η (fun _ => modulus) H ε mesh Cmask
 := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
