-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_affine_ambient_surrogate
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_ambient_surrogate
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T09:56:07.932669+00:00
-- url     : https://prove2.me/theorems/c6e414eb-1145-4ae8-bafd-8bf6dfca128f
-- title:
--   A Lipschitz ambient-torus surrogate for the grid-averaged masked covered profile
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$ ($hR$, $h\sigma$); a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; a finite type $\alpha$ (in a universe $u_\alpha$) with decidable equality and finite families $\mathrm{rowSets}_j$ of subsets of $\alpha$, with row types $\mathrm{rowTypes}_j = \{t : t \in \mathrm{rowSets}_j\}$ and $\mathrm{rows}_j$ the inclusion into $\mathrm{Finset}\,\alpha$; natural-valued $H, \mathrm{step}$ and integer-valued $c$ on `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H > 0$ and each progression $\{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0, \texttt{allocatedPrincipalSides B U b S t})$ ($hsubset$); a natural number $q$ and a label $r :$ tuple index $\to \mathrm{Option}\,\alpha \to \mathbb Z/q$ with $hcell$: the tuples whose residues mod $q$ equal $r$ have positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`; grid is the predicate `allocatedGridAxis U b L_S` on axes and gridLaw is `containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c _ hH hsubset q r hcell grid` (a finite probability law on grid-axis tuples); a point $x : G \to $ `IntegerScalarCubeBox α L_S`; a grid-axis tuple $u_0$ with nonzero gridLaw weight ($hu_0$) and a non-grid-axis tuple $v_0$ (both `PrincipalAxisTuples` for the side lengths `allocatedPrincipalSides B U b S`), with $y_0 = $ `principalAxisJoin grid u₀ v₀`; finite types $Q_j$ and a natural number $d \neq 0$; $hperiod$: $q\cdot\mathbb Z^{\mathrm{rowTypes}_j}$ is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)` for every $j$; $hb$: the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; and $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $Q_j$.
--
--   Let $\mathrm{period} \neq 0$ be a natural number with $\mathrm{period} \mid d$; $\mathrm{rad} \in \mathbb R_{\ge 0}$ with $\mathrm{rad} > 0$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1}v\| \le C_j\|v\|$ and $(|\mathrm{rowSets}_j|+1)\,|\mathcal P(\alpha)|\,C_j(|I_j|+1)\,2\,\mathrm{rad}\,R_j \le 1/4$; $C_{\mathrm{forward}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\texttt{normalizedOrthogonalChart}\ V_j\ b_j\ v\| \le C_{\mathrm{forward}}(j)\|v\|$; $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$; $T : \mathrm{Fin}\,m \to \mathbb R$ with $T_j \ge 0$, `partitionedIdealRadius α m` $+1 \le T_j$, $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}|\cdot 2^{|\alpha|}(|\alpha|+1)^{j+1} \le T_j$ and $|\mathrm{rowSets}_j|\,T_j \le \mathrm{rad}$; $\sigma_j \le 1$ for all $j$; $\rho \in \mathbb R_{\ge 0}$ with $0 < \rho \le 1$; real functions $\mathrm{center}, \mathrm{width}$ on `PrincipalAxisParameter (fun a => ¬ grid a)` with $|\mathrm{center}_i| + |\mathrm{width}_i| \le 1$; a finite type $K_{\mathrm{model}}$, $a : K_{\mathrm{model}} \to \mathbb C$ and $f : K_{\mathrm{model}} \to \mathcal P(\alpha) \to (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$ with every $f_{k,s}$ $L$-Lipschitz ($L \in \mathbb R_{\ge 0}$) and $\|f_{k,s}(z)\| \le 1$; and a real $\eta \ge 0$ such that for every $y$ in `EuclideanJetLayers U rowTypes`,
--   $$\bigl\|\texttt{allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ (allocatedRowSlicedIdeal B U b S rowSets ρ center width)}(y) - \texttt{allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period rad hrad hb o bW a f}(y)\bigr\| \le \eta.$$
--
--   Put $L_{\mathrm{coord}} = K\sum_j C_{\mathrm{forward}}(j)|J_j|$; $L_{\mathrm{cut}} = \bigl(|\texttt{LayerSamplerAxis I n}|\cdot\texttt{normalizedSiteCutoffBound}/(2\,\mathrm{rad})\bigr)L_{\mathrm{coord}}$; $L_{\mathrm{site}} = L_{\mathrm{cut}}\,d + \max(L\,L_{\mathrm{coord}}\,\mathrm{period},\ 4\,\mathrm{period})\cdot\lfloor d/\mathrm{period}\rfloor$; $L_{\mathrm{rows}} = \sum_j |\mathrm{rowSets}_j|$; $\mathrm{mass} = \sum_{\mathrm{label}}\sum_k \|2^{|\mathcal P(\alpha)|}\cdot\texttt{allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k}\|$ over labels $\mathcal P(\alpha) \to (\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}) \times (\prod_j Q_j \to \mathbb Z/\mathrm{period})$; $L_{\mathrm{grid}} = \#\text{grid axes}\cdot|\Sigma_a\,\mathrm{rowTypes}_{a.1}|\cdot 2\,(L_S^{\texttt{layerTailDegree}\ m+1})^2\cdot\sum_j C_{\mathrm{forward}}(j)|J_j|$; and $N = |\texttt{allocatedFullGridNaturalVolume B U b S rowSets}|$ (an explicit product of powers of the grid scales). Then there exists $F : (\texttt{JetAmbientIndex rowTypes J} \to \mathbb R/\mathbb Z) \to \mathbb C$ which is Lipschitz with constant $N\bigl(\mathrm{mass}\,L_{\mathrm{grid}}\,d + \mathrm{mass}\,|\mathcal P(\alpha)|\,L_{\mathrm{site}}\,L_{\mathrm{rows}}\bigr)$, satisfies $\|F(z)\| \le N\,\mathrm{mass}$ for all $z$, and for every $y$ in `EuclideanJetLayers U rowTypes`
--   $$\Bigl\|\mathbb E_{u \sim \mathrm{gridLaw}}\,\Psi_u(y) - F(\texttt{coveredJetAmbientTorus U 1 y})\Bigr\| \le \texttt{allocatedFullGridNaturalVolume B U b S rowSets}\cdot\eta,$$
--   where $\Psi_u = $ `allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (principalAxisJoin grid u v₀) q (allocatedRowSlicedIdeal B U b S rowSets ρ center width)` (a real-valued function defined by OpenAI) and `coveredJetAmbientTorus U 1 y` sends $y$ to its coordinates in the ambient tori $(\mathbb R/\mathbb Z)$ indexed by `JetAmbientIndex rowTypes J` $= \Sigma_j\,\mathrm{rowTypes}_j \times J_j$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_ambient_surrogate` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineBoundedAmbient.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B198` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineBoundedAmbient.lean#L67

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
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
local notation "ig" => allocatedGridIntegerAxis B U b S
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

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "y₀" => principalAxisJoin grid u₀ v₀

include hu₀ hperiod in
theorem exists_allocated_supported_affine_ambient_surrogate
    (period : ℕ) [NeZero period] (hdiv : period ∣ d)
    (rad : ℝ≥0) (hrad : 0 < rad)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (rad : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (rad : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
      (α := α) (fun a => ¬grid a) → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Kmodel : Type*} [Fintype Kmodel] (a : Kmodel → ℂ)
    (f : Kmodel → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hfb : ∀ k s z, ‖f k s z‖ ≤ 1)
    {η : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period rad hrad hb o bW a f y‖ ≤ η) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * rad)) * Lcoord
    let Lsite := Lcut * d + max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let mass := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)),
      ∑ k, ‖(2 : ℂ) ^ Fintype.card (Finset α) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖₊
    let Lgrid := (Fintype.card gridAxes *
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) *
        (2 * ((S.value : ℝ≥0) ^ (layerTailDegree m + 1)) ^ 2))) *
      (∑ j, Cforward j * Fintype.card (J j))
    let N := ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (N * (mass * (Lgrid * d) +
        mass * (Fintype.card (Finset α) * (Lsite * Lrows)))) F ∧
      (∀ z, ‖F z‖ ≤ (N * mass : ℝ≥0)) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u v₀) q (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤
          allocatedFullGridNaturalVolume B U b S rowSets * η := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
