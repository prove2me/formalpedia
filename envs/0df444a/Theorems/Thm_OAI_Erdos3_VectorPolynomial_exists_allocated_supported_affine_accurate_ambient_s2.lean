-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_affine_accurate_ambient_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_ambient_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:49:39.992603+00:00
-- url     : https://prove2.me/theorems/43b632a4-f6b5-497f-a088-1c78e6c4cc9e
-- title:
--   The grid-law mean of the whole masked covered profile is approximated by a Lipschitz bounded function of the ambient torus
-- statement:
--   This statement lives in a large context of data defined by OpenAI; we follow the Lean `variable` declarations. Fix a natural number $m$ and a finite type $G$; for each $j < m$ finite types $I_j$, $J_j$, $E_j$, a natural number $n_j$, a real subspace $U_j$ of $\mathbb{R}^{J_j}$ with Euclidean subspace $V_j$, and a real basis $b_j$ of $V_j^{\perp}$ indexed by $\{0,\dots,n_j-1\}$ whose $\mathbb{Z}$-span is OpenAI's projected integer lattice of $V_j$; finite types $B_a$ with decidable equality for the layer sampler axes $a$ (OpenAI's `LayerSamplerAxis I n`; the axis $(j, c)$ has degree $j+1$); reals $R_j > 0$ and $\sigma_j > 0$; and a layer sampler scale $S$ (main field `S.value`). Let $\alpha$ be a finite type with decidable equality and $\mathrm{rowSets}_j$ a finite set of subsets of $\alpha$ for each $j$; write $\mathrm{rows}_j$ for the inclusion of $\mathrm{rowSets}_j$ into the subsets of $\alpha$. Let `grid` = `allocatedGridAxis U b S.value` (OpenAI). Fix $x : G \to$ `IntegerScalarCubeBox α S.value`, a full principal tuple $y_0$ (OpenAI's `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`), natural numbers $q$, $d \ne 0$, $\mathrm{period} \ne 0$, a real $r > 0$, orthonormal bases $o_j$ of $V_j$ and $\mathbb{Z}$-bases $bW_j$ (indexed by $E_j$) of the lattice sections $\Lambda_j = \mathbb{Z}^{J_j} \cap V_j$. Assume:
--   - for every $j$, $\mathrm{period}\cdot\mathbb{Z}^{\mathrm{rowSets}_j}$ and $q\cdot\mathbb{Z}^{\mathrm{rowSets}_j}$ are contained in the image of the integer matrix `scalarKernelIntegerJet x (j+1) rows_j` (OpenAI);
--   - $M \ge 1$ is a real such that for all $j$ and $z$, $0 \le \mathrm{mask}_j(z) \le M$, where $\mathrm{mask}_j$ = `allocatedIntegerKernelMask B U b S x rows j q (A_j mod q)` is OpenAI's coefficient residue multiplier of the jet matrix above with residue matrix $A_j \bmod q$, and $A_j$ = `allocatedNonkernelJetMatrix B U b S x (y₀ restricted to grid axes) rows j (y₀ restricted to non-grid axes)` (OpenAI);
--   - reals $C_j \ge 0$ with $\lVert \chi_j^{-1}(v) \rVert \le C_j\lVert v \rVert$ for all $v$, where $\chi_j$ = `normalizedOrthogonalChart V_j b_j` (OpenAI), and $(|\mathrm{rowSets}_j| + 1)\cdot 2^{|\alpha|}\cdot C_j\,(|I_j| + 1)\,2rR_j \le 1/4$ for all $j$;
--   - the grid law `gridLaw` (OpenAI's `containedSupportedProgressionAxisLaw` for the grid axes, built from functions $H, \mathrm{step} : (\text{principal indices}) \to \mathbb{N}$, $c$ to $\mathbb{Z}$ with $H > 0$ and every progression $\{c + \mathrm{step}\,k : k < H\}$ inside $\{0,\dots,\mathrm{side} - 1\}$, and residue labels $\mathrm{label}$ modulo $q$ whose residue cell has positive mass under the principal tuple weights with lengths $H$) gives nonzero weight to the restriction of $y_0$ to the grid axes.
--
--   Also fix $\rho \ge 0$ and functions `center`, `width` on the non-grid principal parameters, and let `ideal` = `allocatedRowSlicedIdeal B U b S rowSets ρ center width` (an OpenAI density). The theorem's own hypotheses: $\mathrm{period} \mid d$; constants $C^{\mathrm{fwd}}_j \ge 0$ with $\lVert \chi_j(v) \rVert \le C^{\mathrm{fwd}}_j\lVert v \rVert$; $K \ge 0$ with $R_j^{-1} \le K$; reals $T_j \ge 0$ with `partitionedIdealRadius α m` $+ 1 \le T_j$, (number of exponent vectors of total degree $\le j+1$ in the layer sampler variables)$\cdot 2^{|\alpha|}(|\alpha|+1)^{j+1} \le T_j$, and $|\mathrm{rowSets}_j|\,T_j \le r$; $\sigma_j \le 1$; $0 < \rho \le 1$; $|\mathrm{center}_i| + |\mathrm{width}_i| \le 1$ for all $i$; reals $P_{\mathrm{box}}, P_\rho, V_{\log}, N_{\log}, M_{\log}, \mathrm{target} \ge 0$ with $2\cdot$`allocatedRowSlicedSiteRadius rowSets` $\le e^{P_{\mathrm{box}}}$, $\rho^{-1} \le e^{P_\rho}$, $\mathcal{V} \le e^{V_{\log}}$ where $\mathcal{V}$ = `allocatedFullGridNaturalVolume B U b S rowSets`, $|1/\mathcal{N}| \le e^{N_{\log}}$ where $\mathcal{N}$ = `allocatedProductIdealNormalizer B U b S rowSets`, and $\mathrm{maskCap} \le e^{M_{\log}}$ where $\mathrm{maskCap} = M^{|\mathrm{Axes}|}\cdot$`coefficientDeckPeriodCap rowTypes E period` and $|\mathrm{Axes}|$ is the number of layer sampler axes (all OpenAI quantities).
--
--   Define $p = P_{\mathrm{box}} + P_\rho + V_{\log} + N_{\log} + M_{\log} + \mathrm{target}$; $Q$ = `idealSiteLogBudget (Σ_a |rowSets_{j(a)}|) |α| p` $= |\alpha| + (\sum_a |\mathrm{rowSets}_{j(a)}|)\,p +$ `affineProfileLogBound (Σ_a |rowSets_{j(a)}|) p` $+ p + 1$ (sums over all axes $a = (j(a), \cdot)$); $A = \exp\bigl(2^{|\alpha|}|\mathrm{Axes}|\,(4Q + 8) + Q\bigr)$; $\mathrm{mass} = \max\bigl(0,\ 2^{2^{|\alpha|}}\cdot|1/\mathcal{N}|\cdot \mathrm{period}^{(\sum_j n_j + \sum_j |E_j|)\,2^{|\alpha|}}\cdot\mathrm{maskCap}\cdot A\bigr)$; $L = e^{|\mathrm{Axes}| + 6Q + 12} + |\mathrm{Axes}|\cdot\kappa_{\mathrm{cut}}/(2\,\mathrm{siteRadius})$ with $\kappa_{\mathrm{cut}}$ = `normalizedSiteCutoffBound` and $\mathrm{siteRadius}$ = `allocatedRowSlicedSiteRadius rowSets`; $L_{\mathrm{coord}} = K\sum_j C^{\mathrm{fwd}}_j|J_j|$; $L_{\mathrm{site}} = (|\mathrm{Axes}|\,\kappa_{\mathrm{cut}}/(2r))\,L_{\mathrm{coord}}\,d + \max(L\,L_{\mathrm{coord}}\,\mathrm{period},\ 4\,\mathrm{period})\cdot\lfloor d/\mathrm{period}\rfloor$; $L_{\mathrm{rows}} = \sum_j |\mathrm{rowSets}_j|$; $L_{\mathrm{grid}} = |\mathrm{gridAxes}|\cdot(\sum_a |\mathrm{rowSets}_{j(a)}|)\cdot 2\,\bigl(\texttt{S.value}^{\texttt{layerTailDegree}\ m + 1}\bigr)^2\cdot\sum_j C^{\mathrm{fwd}}_j|J_j|$; and $\mathcal{N}_V = |\mathcal{V}|$. (In these formulas the number of subsets of $\alpha$ is $2^{|\alpha|}$; all quantities are nonnegative reals.)
--
--   Then there exists $F : (\text{functions from } \Sigma_j\, \mathrm{rowSets}_j \times J_j \text{ to } \mathbb{R}/\mathbb{Z}) \to \mathbb{C}$ such that
--   - $F$ is Lipschitz with constant $\mathcal{N}_V\bigl(\mathrm{mass}\cdot L_{\mathrm{grid}}\, d + \mathrm{mass}\cdot 2^{|\alpha|}\,L_{\mathrm{site}}\,L_{\mathrm{rows}}\bigr)$;
--   - $|F(z)| \le \mathcal{N}_V\cdot\mathrm{mass}$ for all $z$;
--   - for every $y$ in OpenAI's `EuclideanJetLayers U rowTypes` (for each $j$ and each $t \in \mathrm{rowSets}_j$ a point of the torus $V_j/\Lambda_j$),
--   $$\Bigl|\,\mathbb{E}_{u \sim \mathrm{gridLaw}}\, \texttt{allocatedWholeMaskedCoveredProfile}\ \ldots\ d\ \bigl(\texttt{principalAxisJoin grid}\ u\ (y_0|_{\neg\mathrm{grid}})\bigr)\ q\ \mathrm{ideal}\ y \;-\; F\bigl(\texttt{coveredJetAmbientTorus}\ U\ 1\ y\bigr)\Bigr| \le e^{-\mathrm{target}},$$
--   where `allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y' q f` is OpenAI's real-valued covered profile density on the tori (built from $y'$ restricted to grid and non-grid axes, the long profile density of $f$ with the residue matrices $A_j \bmod q$ computed from $y'$, and cover level $d$), `principalAxisJoin grid u v` is the full tuple equal to $u$ on grid axes and $v$ elsewhere, and `coveredJetAmbientTorus U 1 y` sends $y$ to its coordinates in $(\mathbb{R}/\mathbb{Z})^{\Sigma_j \mathrm{rowSets}_j \times J_j}$ (OpenAI).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_ambient_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_ambient` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineBoundedAmbient.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B216`, `OAIE3v2B217` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineBoundedAmbient.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_ambient)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

include hr hperiod hM hm hR hC hchart hbudget hu₀ hmodulus in

theorem exists_allocated_supported_affine_accurate_ambient_s2
    (hdiv : period ∣ d)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Pbox Prho Vlog Nlog Mlog target : ℝ}
    (hPbox : 0 ≤ Pbox) (hPrho : 0 ≤ Prho) (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog) (htarget : 0 ≤ target)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖inverseNormalizer‖ ≤ Real.exp Nlog)
    (hmask : M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period ≤ Real.exp Mlog) :
    let p := Pbox + Prho + Vlog + Nlog + Mlog + target
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    let mass := Real.toNNReal ((2 : ℝ) ^ Fintype.card (Finset α) * ‖inverseNormalizer‖ *
      ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
        Fintype.card (Finset α) * maskCap * A))
    let L : ℝ≥0 := ⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ +
      Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * allocatedRowSlicedSiteRadius rowSets)
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lsite := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord * d +
      max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
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
          (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤
          Real.exp (-target) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
