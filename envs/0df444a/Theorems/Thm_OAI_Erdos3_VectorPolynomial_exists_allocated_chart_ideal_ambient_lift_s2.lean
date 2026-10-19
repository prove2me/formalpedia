-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_chart_ideal_ambient_lift_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_chart_ideal_ambient_lift_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:49:20.182553+00:00
-- url     : https://prove2.me/theorems/dcf3c4f4-2b45-4353-806d-4c2d7902e278
-- title:
--   The allocated product chart ideal approximation lifts to a bounded Lipschitz function on the ambient jet torus
-- statement:
--   Fix the data of OpenAI's allocated layer-sampler setup: a natural number $m$; finite types $G$, $I_j$, $J_j$, $E_j$ ($j < m$), $B(a)$ for each layer-sampler axis $a$, and $\alpha$ (finite, with decidable equality); dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases $b_j$ (indexed by $\{0,\dots,n_j-1\}$) of the orthogonal complement of $U_j$ with $hb$: the $\mathbb{Z}$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ (indexed by $I_j$) of $U_j$; $\mathbb{Z}$-bases $bW_j$ (indexed by $E_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; reals $R_j, \sigma_j$; a `LayerSamplerScale B U b R σ` $S$; finite sets `rowSets j` of subsets of $\alpha$ (viewed as types $\mathrm{rowTypes}_j$); a point $x : G \to$ `IntegerScalarCubeBox α S.value`; a principal integer tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`; natural numbers $q$, $d \ne 0$, $\mathrm{period} \ne 0$; and $r \in \mathbb{R}_{\ge 0}$ with $r > 0$.
--
--   Assume $\mathrm{period}$ divides $d$, and $R_j > 0$ for all $j$. Let $C_j \ge 0$ be reals with $\lVert \texttt{normalizedOrthogonalChart}(U_j, b_j)^{-1}(v)\rVert \le C_j \lVert v\rVert$ and $C_j (\lvert I_j\rvert + 1)(2 r R_j) \le 1/4$ for all $j, v$; let $C^{\mathrm{fwd}}_j \in \mathbb{R}_{\ge 0}$ with $\lVert \texttt{normalizedOrthogonalChart}(U_j, b_j)(v)\rVert \le C^{\mathrm{fwd}}_j \lVert v\rVert$ for all $j, v$; and let $K \in \mathbb{R}_{\ge 0}$ with $R_j^{-1} \le K$ for all $j$. Let $T$ be a finite type, $a : T \to \mathbb{C}$, and $f(k, s, \cdot)$, for $k \in T$ and $s \subseteq \alpha$, complex functions on $\mathbb{R}^{\text{axes}}$ (axes = `LayerSamplerAxis I n`) that are $L$-Lipschitz (for some $L \in \mathbb{R}_{\ge 0}$) and bounded in norm by $1$.
--
--   Define
--   - $L_{\mathrm{coord}} = K \sum_j C^{\mathrm{fwd}}_j \lvert J_j\rvert$;
--   - $L_{\mathrm{cut}} = (\lvert\text{axes}\rvert \cdot \texttt{normalizedSiteCutoffBound} / (2r)) \cdot L_{\mathrm{coord}}$, where `normalizedSiteCutoffBound` is a constant defined by OpenAI;
--   - $L_{\mathrm{site}} = L_{\mathrm{cut}}\, d + \max(L\, L_{\mathrm{coord}}\, \mathrm{period},\ 4\,\mathrm{period}) \cdot \lfloor d/\mathrm{period}\rfloor$ (natural-number division);
--   - $L_{\mathrm{rows}} = \sum_j \lvert \texttt{rowSets}\ j\rvert$;
--   - $\mathrm{mass} = \sum_{\mathrm{label}} \sum_{k \in T} \bigl\lVert 2^{\lvert \mathcal{P}(\alpha)\rvert} \cdot \texttt{allocatedProductMaskedIdealCoefficient B U b S rowSets x y0 q d period a label k} \bigr\rVert$, where label ranges over all functions from subsets of $\alpha$ to pairs (an element of $\prod_j (\mathbb{Z}/\mathrm{period})^{n_j}$, an element of $\prod_j (\mathbb{Z}/\mathrm{period})^{E_j}$), and $\lvert\mathcal{P}(\alpha)\rvert = 2^{\lvert\alpha\rvert}$ is the number of subsets of $\alpha$.
--
--   Then there exists a function $F$ from `JetAmbientIndex rowTypes J → UnitAddCircle` to $\mathbb{C}$ which is Lipschitz with constant $\mathrm{mass} \cdot (\lvert\mathcal{P}(\alpha)\rvert \cdot L_{\mathrm{site}} \cdot L_{\mathrm{rows}})$, satisfies $\lVert F(z)\rVert \le \mathrm{mass}$ for all $z$, and satisfies, for every $y$ in `EuclideanJetLayers U rowTypes`,
--   $$\texttt{allocatedProductChartIdealApproximation B U b S rowSets x y0 q d period r hr hb o bW a f}\ y = F(\texttt{coveredJetAmbientTorus U 1 y}).$$
--   All named objects are defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_chart_ideal_ambient_lift_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocated_chart_ideal_ambient_lift` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedChartIdealAmbientLift.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B216` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedChartIdealAmbientLift.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocated_chart_ideal_ambient_lift)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216

section

namespace OAI

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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem exists_allocated_chart_ideal_ambient_lift_s2
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lsite := Lcut * d + max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let mass := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ k, ‖(2 : ℂ) ^ Fintype.card (Finset α) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (mass * (Fintype.card (Finset α) * (Lsite * Lrows))) F ∧
      (∀ z, ‖F z‖ ≤ mass) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y =
          F (coveredJetAmbientTorus U 1 y) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
