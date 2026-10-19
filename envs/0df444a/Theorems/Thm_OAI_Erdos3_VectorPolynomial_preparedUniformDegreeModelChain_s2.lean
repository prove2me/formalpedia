-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeModelChain_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedUniformDegreeModelChain_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:26:39.314592+00:00
-- url     : https://prove2.me/theorems/402fdaae-5ca0-4e0e-8c23-a733d3f75cdc
-- title:
--   The shared-width direct detection interface with halved threshold implies the shared-width centered forecast model interface
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ be a finite type with decidable equality; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types (in `Type`), $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $\mathrm{basis}_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (defined by OpenAI, with natural-number value `S.value`). Let $n_X \in \mathbb{N}$, $\mathrm{selection} : \mathrm{Fin}\,1 \hookrightarrow G$, $\mathrm{stride}, N : \mathrm{Fin}(n_X) \to \mathbb{N}$, $P_{\mathrm{detect}}$ a polynomial with natural-number coefficients, $u_{\mathrm{Source}}, p_{\mathrm{Model}}, p_{\mathrm{Slice}}$ reals, $V_{\mathrm{tail}} : \mathrm{Fin}\,m \to \mathbb{R}_{\ge 0}$, and $\tau, u, p, \mathrm{forecastCap}$ reals. Write $K$ = `LayerSamplerVariables G I n B`,
--   $$C_{\mathrm{tail}} = 4 \prod_j \texttt{earlyConstantDensityCap}\ |I_j|\ n_j\ R_j\ V_{\mathrm{tail},j}, \qquad K_{\mathrm{slice}} = e^{p_{\mathrm{Slice}} |K|},$$
--   where `earlyConstantDensityCap a n R V` $= V\,(R/4)^{-a}\,\bigl(8\cdot\texttt{probabilityProfileLipschitz}/(R/4)\bigr)^{n}$, and $\alpha$ = `forecastAugmentedUnitThreshold u p K_slice (max 1 C_tail) forecastCap` (defined by OpenAI as $\bigl(e^{-(u+3)}/e^{2p}\bigr)/\max\bigl(1, (2 K_{\mathrm{slice}} \max(1, C_{\mathrm{tail}}) + \mathrm{forecastCap})/e^{-(u+3)}\bigr)$). Assume (hypothesis $h_b$) that the $\mathbb{Z}$-span of $\mathrm{basis}_j$ is the projected integer lattice `projectedIntegerLattice` of $U_j$ for all $j$; let $o_j$ be an orthonormal basis of $U_j$ indexed by $I_j$; assume that each lattice $\Gamma_j$ = section of $\mathbb{Z}^{J_j}$ by $U_j$ is a full lattice in $U_j$, and let $\nu_j$ be a left-invariant probability measure on $U_j / \Gamma_j$ (these $\nu_j$ are arguments of the theorem but do not appear in its statement otherwise). Let the coefficient torus `CoefficientTorus U` (for the variables $K$; defined by OpenAI) carry a Borel σ-algebra and be compact, and let $\mu$ be a left-invariant probability measure on it.
--
--   **Hypotheses.** Let $P_{\mathrm{chart}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}, P_{\mathrm{late}}, p_{\mathrm{Gain}}, P_{\mathrm{physical}}, \mathrm{coarseTarget}$ be reals and assume:
--   - `PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface` holds for all the data above (with $u := u_{\mathrm{Source}}$ and threshold $\alpha/2$) and the parameters $P_{\mathrm{chart}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}, P_{\mathrm{late}}, p_{\mathrm{Gain}}, P_{\mathrm{physical}}, \mathrm{coarseTarget}$. This is a proposition defined by OpenAI: for all positive strides bounded by $e^{Q_{\mathrm{stride}}}$, all chart constants bounded by $e^{P_{\mathrm{chart}}}$, all admissible spatial scales $\tau$ and narrow widths, all nonempty cell sets and all layer polynomials of sufficient sampling rank, it asserts the existence of a normalized original path law on the trimmed integer box together with detection properties for it;
--   - $D$ is a real with $0 \le P_{\mathrm{master}} \le P_{\mathrm{late}}$, `AllocatedComparisonDimensions B (Fin 1) selectedRows D` (defined by OpenAI: $D \ge 0$ and $D$ bounds $m$, $|G|$, $1$, the number of axes, tuples, parameters, outputs and rows), where $\mathrm{selectedRows}_j$ is the type of elements of `boundedBooleanJetRows (Fin 1) (j+1)`;
--   - $D \le P_{\mathrm{master}}$, $n_X \le P_{\mathrm{master}}$, $P_{\mathrm{chart}} \le P_{\mathrm{master}}$, $Q_{\mathrm{stride}} \le P_{\mathrm{master}}$, $P_{\mathrm{physical}} \le P_{\mathrm{master}}$;
--   - $R_j^{-1} \le e^{P_{\mathrm{master}}}$ and $\sigma_j^{-1} \le e^{P_{\mathrm{late}}}$ for all $j$; $S.\mathrm{value} \le e^{P_{\mathrm{late}}}$; $\sigma_j \le 1$ for all $j$;
--   - for every $C : \mathrm{Fin}\,m \to \mathbb{R}$ with $0 \le C_j \le e^{P_{\mathrm{chart}}}$ for all $j$, we have $C_j (|I_j| + 1) R_j \le 1/4$ for all $j$;
--   - $0 \le u$, $0 \le p$, $p_{\mathrm{Slice}} |K| \le p$, $C_{\mathrm{tail}} \le e^{p}$, $0 \le \mathrm{forecastCap} \le e^{p}$.
--
--   **Conclusion.** `SharedWidthPreparedCenteredForecastModelInterface` holds for the same data (with $u_{\mathrm{Source}}$, $u$, $p$, $\mathrm{forecastCap}$ and $\mu$) and the parameters $P_{\mathrm{chart}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}, P_{\mathrm{late}}, p_{\mathrm{Gain}}, P_{\mathrm{physical}}, \mathrm{coarseTarget}$. This is a proposition defined by OpenAI with leading quantifiers of the same kind as the detection interface (with an additional real $E$), asserting the existence of normalized centered path laws, with normalizers within $e^{-E}$ of $1$, and of a centered forecast model for the shared-width prepared source.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeModelChain_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeModelChain` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeProductiveSourceModel.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B285`, `OAIE3v2B286` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeProductiveSourceModel.lean (declaration OAI.Erdos3.VectorPolynomial.preparedUniformDegreeModelChain)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Definitions.Def_OAIE3v2B286

section

namespace OAI

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ u p forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

include ν in

theorem preparedUniformDegreeModelChain_s2
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) («α» := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    {D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) selectedRows D)
    (hD : D ≤ Pmaster) (hnX : (nX : ℝ) ≤ Pmaster)
    (hChartMaster : Pchart ≤ Pmaster) (hStrideMaster : Qstride ≤ Pmaster)
    (hPhysicalMaster : Pphysical ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate) (hσone : ∀ j, σ j ≤ 1)
    (hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p) :
    SharedWidthPreparedCenteredForecastModelInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  sorry

end Erdos3.VectorPolynomial

end OAI
end
