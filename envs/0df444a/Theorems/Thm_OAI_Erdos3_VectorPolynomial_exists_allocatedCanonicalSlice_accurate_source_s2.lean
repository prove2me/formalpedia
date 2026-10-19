-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_accurate_source_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_accurate_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:59:12.595163+00:00
-- url     : https://prove2.me/theorems/792e4fe1-3009-4bd0-be0b-17c62487a95d
-- title:
--   Accurate site and ideal expansions exist for the canonical slice, with explicit budgets
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); $\mathrm{dim} \in \mathbb N$, with $\mathrm{rowSets}_j =$ `boundedBooleanJetRows (Fin dim) (j+1)` (subsets of size at most $j+1$) and rowTypes$_j$ its subtype; grid the predicate `allocatedGridAxis U b S.value` and gridAxes the grid axes; finite types $E_j$; $q \in \mathbb N$ and natural numbers $d, \mathrm{period} \ne 0$; $r \in \mathbb R_{>0}$ (hr); $\mathbb Z$-span of $b_j$ equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$ (indexed by $E_j$) of $\Lambda_j =$ `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, each $\Lambda_j$ a $\mathbb Z$-lattice; $C : \mathrm{Fin}\,m \to \mathbb R$ with $C_j \ge 0$ (hC), $\|(\texttt{normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)})^{-1}v\| \le C_j\|v\|$ (hchart) and $(|\mathrm{rowSets}_j|+1)\cdot 2^{\mathrm{dim}}\cdot C_j(|I_j|+1)\cdot 2rR_j \le 1/4$ (hbudget) for all $j$; $\rho \in \mathbb R_{\ge 0}$ and real functions center, width on `PrincipalAxisParameter (¬ grid)` (with $\alpha = \mathrm{Fin}\,\mathrm{dim}$); $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $c : \mathrm{FullInput} \to \mathbb Z$ (FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`) with $H > 0$ (hH) and each `integerProgressionSupport (c t) (step t) (H t)` contained in $[0,$ `allocatedPrincipalSides B U b S t`$)$ (hsubset); and a residue label $\lambda : \mathrm{FullInput} \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/q$ whose cell has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hcell). Write gridLaw $=$ `containedSupportedProgressionAxisLaw … H step c … hH hsubset q λ hcell grid`, ideal $=$ `allocatedRowSlicedIdeal B U b S rowSets ρ center width`, and invN $=$ `allocatedProductIdealNormalizer B U b S rowSets`$^{-1}$.
--
--   **Hypotheses.** $C_{\mathrm{fwd}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\texttt{normalizedOrthogonalChart …}\,v\| \le C_{\mathrm{fwd},j}\|v\|$; $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$; $Q_{\mathrm{grid}} \in \mathbb R_{\ge 0}$ with $8(|\texttt{layerIntegerPrincipalSlots B j i}|+1) \le Q_{\mathrm{grid}}$ for every grid axis $\langle j, \mathrm{inr}\,i\rangle$; $\mathrm{dim} \le m+1$; $\delta_g > 0$ with $\delta_g\cdot$`allocatedPrincipalSides B U b S t` $\le H_t$ for all $t$; $T_g \in \mathbb N$ with $(\mathrm{dim}+1)q/\delta_g \le T_g$; $\mathrm{step}_t > 0$ for all $t$; $A_g \in \mathbb R_{\ge 0}$ with `Real.smoothTransition` $A_g$-Lipschitz; $P_g \ge 1$ with `scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1` $\le P_g$, `scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 q` $\le P_g$ and $\mathrm{step}_t\,q \le P_g$; for all $j, i$, `positiveModerateSpectrumBlockCount j |rowSets j| ((layerTailDegree m + 1)|rowSets j|)` and `uniformSpectrumBlockCount j |rowSets j| ((j+1)|rowSets j|)` are at most $|B_{\langle j,\mathrm{inr}\,i\rangle}|$; reals $D_g, v_g, w_g, t_g, p_g \ge 0$ with $\mathrm{dim}, j+1, |\mathrm{rowSets}_j|$, `layerTailDegree m` $+1$, $|B_{\langle j,\mathrm{inr}\,i\rangle}|$, $|\mathrm{gridAxes}|$, $|\texttt{LayerSamplerAxis I n}|$, $|\Sigma_a\mathrm{rowTypes}_{\mathrm{layer}(a)}|$, $\sum_j|J_j|$ and `probabilityProfileLipschitz` all $\le D_g$, and $R_j, R_j^{-1}, |\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \le e^{v_g}$, $\delta_g^{-1} \le e^{w_g}$, $T_g \le e^{t_g}$, $P_g \le e^{p_g}$; a real $B_{\mathrm{an}} \ge D_g \ge 0$ with `normalizedSiteCutoffBound` $\le e^{B_{\mathrm{an}}}$, $K\sum_j C_{\mathrm{fwd},j}|J_j| \le e^{B_{\mathrm{an}}}$ and $Q_{\mathrm{grid}} \le e^{B_{\mathrm{an}}}$; $1 \le r$; $\sigma_j \le 1$ for all $j$ (stated twice); $T : \mathrm{Fin}\,m \to \mathbb R$ with $T_j \ge 0$, `partitionedIdealRadius (Fin dim) m` $+1 \le T_j$, $|\texttt{BoundedCoefficientExponent …(j+1)}|\cdot 2^{\mathrm{dim}}(\mathrm{dim}+1)^{j+1} \le T_j$ and $|\mathrm{rowSets}_j|\,T_j \le r$; $0 < \rho \le 1$ and $|\mathrm{center}(i)| + |\mathrm{width}(i)| \le 1$ for all $i$; $P_\rho \ge 0$ with $\rho^{-1} \le e^{P_\rho}$; reals $P_{\mathrm{num}}, P_k, \mathrm{target} \ge 0$; $M_k \in \mathbb N$ with $0 < M_k \le e^{P_k}$; $|I_j|, n_j, |\texttt{BoundedCoefficientExponent …(j+1)}| \le P_{\mathrm{num}}$, and $R_j^{-1}$, `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le e^{P_{\mathrm{num}}}$; a point $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value` and an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x` (hx); a finite type $X$ and $\mathrm{stride} : X \to \mathbb N$ with positive values; $q =$ `canonicalSlicedModulus selection stride m x` (with $M = M_k$); $\mathrm{period} =$ `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hx m)`; $\mathrm{period} \mid d$; and a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)` of positive weight under `containedSupportedProgressionLaw … H step c … hH hsubset q λ hcell`.
--
--   **Constants.** $A_{\mathrm{mass}}$ and $A_{\mathrm{an}}$ are the natural numbers chosen by OpenAI's lemmas `exists_allocatedAffineModelMass_budget m dim` and `exists_allocatedAffineAnalytic_budget m dim`. $F = m\,2^{\mathrm{dim}}(P_{\mathrm{num}}+8)(1+4P_{\mathrm{num}}) + |\texttt{LayerSamplerAxis I n}|\cdot m2^{m+1}P_k + \sum_j |E_j|\cdot|\mathrm{rowTypes}_j|\cdot(m+1)P_k$; $D_{\mathrm{out}} = |\Sigma_a\,\mathrm{rowTypes}_{\mathrm{layer}(a)}|$; $D_{\mathrm{grid}} = |\texttt{LayerSamplerAxis I n}|$; $P_{\mathrm{box}} = (m+2)\mathrm{dim} + m + 4$; $E_g = D_{\mathrm{out}}P_\rho + \mathrm{target} + F + 1$; $p =$ `slicedGridGeometryLog Dg vg wg tg` $+ p_g$; $L_j(e) =$ `slicedGridSiteLog j |rowSets j| ((layerTailDegree m + 1)|rowSets j|) ((j+1)|rowSets j|) Dg p e`; $C_p = \sum_j(L_j(0) + D_g(v_g+1))$; $E_g' =$ `uniformProductAccuracyLog Dg Cp Eg` $+ D_g(v_g+1) + 1$; $O_p = \sum_j(\texttt{siteExponentialOutputLog}(2^{\mathrm{dim}}, L_j(E_g')) + (D_g+1)(v_g+1))$; $G_{\mathrm{cost}} = D_{\mathrm{grid}}\max(O_p, 0)$; $\varepsilon = \exp(-(G_{\mathrm{cost}} + \mathrm{target} + F + 1))$; $P_{\mathrm{long}} = P_{\mathrm{box}} + P_\rho + G_{\mathrm{cost}} + \mathrm{target} + F + 2$.
--
--   **Conclusion.** There is a family $e$ of `ScalarSiteExpansion`s on $\mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim})$ indexed by gridAxes, each satisfying `Bounds` $(e^{O_p}, e^{O_p}, e^{O_p}, e^{O_p}, \exp(\texttt{slicedGridGeometryLog Dg vg wg tg} + D_g + v_g + 8))$, such that, with $\rho_s =$ `allocatedRowSlicedSiteRadius rowSets`, $L_{\mathrm{cut}} = |\texttt{LayerSamplerAxis I n}|\cdot$`normalizedSiteCutoffBound`$/(2\rho_s)$, $Q =$ `idealSiteLogBudget D_out dim P_long`, $N_{ax} = |\texttt{LayerSamplerAxis I n}|$, $A = \exp(2^{\mathrm{dim}}N_{ax}(4Q+8) + Q)$ and $\mathrm{maskCap} =$ `layerKernelIndexBound m Mk`$^{N_{ax}}\cdot$`coefficientDeckPeriodCap rowTypes E period`, there exist $k \in \mathbb N$ with $k \le e^{4Q+8}$ and $|\mathrm{Fin}\,k|^{2^{\mathrm{dim}}N_{ax}} \le \exp(2^{\mathrm{dim}}N_{ax}(4Q+8))$, and, writing $\mathcal I = (\mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim}) \times \texttt{LayerSamplerAxis I n} \to \mathrm{Fin}\,k)$, there exist $a : \mathcal I \to \mathbb C$ and $f : \mathcal I \to \mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb R^{\texttt{LayerSamplerAxis I n}} \to \mathbb C$ such that:
--
--   1. $\sum_i\|a_i\| \le A$; $\|f(i,s,v)\| \le 1$; each $f(i,s)$ is $(\exp(N_{ax} + 6Q + 12) + L_{\mathrm{cut}})$-Lipschitz; and $f(i,s,v) = 0$ whenever $|v_j| > 2\rho_s$ for some $j$;
--   2. $\sum_{\ell}\sum_i\|\texttt{allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a ℓ i}\| \le \|\mathrm{invN}\|\cdot|\mathrm{Lab}|^{2^{\mathrm{dim}}}\cdot\mathrm{maskCap}\cdot A$, where $\ell$ ranges over labels $\mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim}) \to \mathrm{Lab}$, $\mathrm{Lab} = (\prod_j(\mathbb Z/\mathrm{period})^{\mathrm{Fin}(n_j)})\times(\prod_j(\mathbb Z/\mathrm{period})^{E_j})$;
--   3. $\Sigma := \sum_{\ell, i, k_g}\|2^{2^{\mathrm{dim}}}\cdot\texttt{allocatedProductMaskedIdealCoefficient …}\ \ell\ i\cdot\texttt{coverSiteCoefficient e k_g}\|$ satisfies both $\Sigma \le \exp\bigl(2\cdot 2^{\mathrm{dim}} + F + 2^{\mathrm{dim}}(\sum_j|J_j|)(m+1)P_k + 2^{\mathrm{dim}}N_{ax}(4Q+8) + Q + |\mathrm{gridAxes}|\,O_p\bigr)$ and $\Sigma \le \exp((D_g + p + v_g + F + P_\rho + P_k + \mathrm{target} + A_{\mathrm{mass}})^{A_{\mathrm{mass}}})$;
--   4. every `allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period ℓ (f i s)` has norm at most $1$ everywhere and is measurable, and `allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f` (call it $\mathcal A$) is measurable;
--   5. for every $y$ in `EuclideanJetLayers U rowTypes`, $\|\texttt{allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal}\ y - \mathcal A(y)\| \le \|\mathrm{invN}\|\cdot\mathrm{maskCap}\cdot\varepsilon$;
--   6. for every such $y$, $\bigl\|\mathrm{gridLaw.mean}\bigl(u \mapsto \texttt{allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d}\ (\texttt{principalAxisJoin grid u}\ (\texttt{principalAxisRestrict (¬ grid) y₀}))\ q\ \mathrm{ideal}\ y\bigr) - \mathcal A(y)\cdot\texttt{allocatedFullGridChartModel B U b S rowSets d hb o bW e}\ y\bigr\| \le e^{-\mathrm{target}}$;
--   7. for every type $X'$ and `VectorPolynomial X' ℝ (J j → ℝ)`s $\mathrm{poly}_j$ of degree at most $j+1$ (`DegreeLE 1 (j+1)`) with all coefficients in $U_j$ (hm), putting $L_{\mathrm{coord}} = K\sum_j C_{\mathrm{fwd},j}|J_j|$, $L_{\mathrm{long}} = (N_{ax}\cdot\texttt{normalizedSiteCutoffBound}/(2r))L_{\mathrm{coord}} + \max\bigl((\exp(N_{ax}+6Q+12) + L_{\mathrm{cut}})L_{\mathrm{coord}}M_k^{m+1},\ 4M_k^{m+1}\bigr)$, $L_{\mathrm{prim}} = e^{O_p}$ and $L_{\mathrm{grid}} = \max\bigl(|\mathrm{gridAxes}|\,L_{\mathrm{prim}}Q_{\mathrm{grid}}L_{\mathrm{coord}}L_{\mathrm{prim}}^{|\mathrm{gridAxes}|},\ 4L_{\mathrm{prim}}^{|\mathrm{gridAxes}|}\bigr)$, and $\Phi = \exp((D_g + p + v_g + F + P_\rho + P_k + \mathrm{target} + B_{\mathrm{an}} + A_{\mathrm{an}})^{A_{\mathrm{an}}})$: we have $(L_{\mathrm{long}} + L_{\mathrm{grid}})\cdot\mathrm{period}\cdot L_{\mathrm{prim}}^{|\mathrm{gridAxes}|} \le \Phi$ and $\mathrm{period}\cdot e^{O_p|\mathrm{gridAxes}|} \le \Phi$, and there exists $g$, assigning to each label $\ell$, $i \in \mathcal I$, term choice $k_g$ of $e$ and site $t$ a function on $((\texttt{JetAmbientIndex (fun _ => Unit) J} \to \mathbb R/\mathbb Z) \times (\Sigma_j J_j \to \mathbb R/\mathbb Z)) \times (\Sigma_j J_j \to \mathbb R/\mathbb Z)$ with values in $\mathbb C$, each $(L_{\mathrm{long}} + L_{\mathrm{grid}})$-Lipschitz and of norm at most $1$, such that `AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f poly hm g` holds.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_accurate_source_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_accurate_source` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedFiniteSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedFiniteSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_accurate_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := (Fin dim)) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

include hR hC hchart hbudget in

theorem exists_allocatedCanonicalSlice_accurate_source_s2
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Qgrid)
    (hdim : dim ≤ m + 1)
    {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U b S tg ≤ (H tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin dim) + 1) * q : ℕ) : ℝ) / δg ≤ Tg)
    (hstep : ∀ tg, 0 < step tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 q ≤ Pg)
    (hstride : ∀ tg, ((step tg * q : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin dim) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxes : (Fintype.card gridAxes : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ} (hBanalytic : 0 ≤ Banalytic) (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic) (hrone : 1 ≤ r)
    (hσgrid : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) (hTideal : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (boundedBooleanJetRows (Fin dim) (j.val + 1)).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Prho : ℝ} (hPrho : 0 ≤ Prho) (hρPrho : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    {Pnum Pk target : ℝ} (hPnum : 0 ≤ Pnum) (hPk : 0 ≤ Pk) (htarget : 0 ≤ target)
    {Mk : ℕ} (hMk : 0 < Mk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum)
    (x : G → IntegerScalarCubeBox (Fin dim) S.value) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    {X : Type*} [Fintype X] (stride : X → ℕ) (hstridepos : ∀ i, 0 < stride i)
    (hqcanonical : q = canonicalSlicedModulus (M := Mk) selection stride m x)
    (hperiodcanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
    (hdiv : period ∣ d)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
      hH hsubset q label hcell).weight y₀) :
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m dim)
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m dim)
    let F := (m * (2 : ℝ) ^ Fintype.card (Fin dim)) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * ((m + 1 : ℕ) * Pk))
    let Dout := (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ)
    let Dgrid := (Fintype.card (LayerSamplerAxis I n) : ℝ)
    let Pbox := ((m : ℝ) + 2) * Fintype.card (Fin dim) + m + 4
    let Eg := Dout * Prho + (target + F) + 1
    let _εgrid := Real.exp (-Eg)
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) Dg p e
    let Cp := ∑ j, (L j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (L j Eg') + (Dg + 1) * (vg + 1))
    let Gcost := Dgrid * max Op 0
    let ε := Real.exp (-(Gcost + (target + F) + 1))
    let Plong := Pbox + Prho + Gcost + (target + F) + 2
    ∃ e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
    let sourceRadius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card (Fin dim)) Plong
    let A := Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin dim)) * maskCap * A) ∧
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e kg‖) ≤
          Real.exp (2 * Fintype.card (Finset (Fin dim)) + F +
            Fintype.card (Finset (Fin dim)) * ((∑ j, Fintype.card (J j) : ℕ) * ((m + 1 : ℕ) * Pk)) +
            ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) +
            Fintype.card gridAxes * Op) ∧
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e kg‖) ≤
          Real.exp ((Dg + p + vg + F + Prho + Pk + target + Amass) ^ Amass) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            Real.exp (-target)) ∧
        ∀ {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
          (hm : ∀ j e, coefficients (poly j) e ∈ U j),
          let Lcoord : ℝ≥0 := K * ∑ j, Cforward j * Fintype.card (J j)
          let Llong : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
            max ((⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) * Lcoord * (Mk ^ (m + 1) : ℝ≥0)) (4 * (Mk ^ (m + 1) : ℝ≥0))
          let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg Op⟩
          let Lgrid : ℝ≥0 := max ((((Fintype.card gridAxes : ℝ≥0) * Lprimitive) * Qgrid) *
            Lcoord * Lprimitive ^ Fintype.card gridAxes) (4 * Lprimitive ^ Fintype.card gridAxes)
          (((Llong + Lgrid) * (period * Lprimitive ^ Fintype.card gridAxes) : ℝ≥0) : ℝ) ≤
            Real.exp ((Dg + p + vg + F + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic) ∧
          (period : ℝ) * (Real.exp Op) ^ Fintype.card gridAxes ≤
            Real.exp ((Dg + p + vg + F + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic) ∧
          ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
              (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → (∀ a, (e a).Term) → Finset (Fin dim) →
              (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
                ((Σ j, J j) → UnitAddCircle)) → ℂ,
            (∀ label i kg t, LipschitzWith (Llong + Lgrid) (g label i kg t)) ∧
            (∀ label i kg t z, ‖g label i kg t z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f poly hm g := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
