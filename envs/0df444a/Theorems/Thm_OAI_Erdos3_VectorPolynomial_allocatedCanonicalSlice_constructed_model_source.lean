-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCanonicalSlice_constructed_model_source
-- name    : OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_constructed_model_source
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T09:51:22.873974+00:00
-- url     : https://prove2.me/theorems/0baefa0b-d450-403c-9142-4e3ecbfac605
-- title:
--   The constructed canonical-slice model source is within exp(-lossTarget) of the profile bound
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); $\mathrm{dim} \in \mathbb N$ and finite families $\mathrm{rowSets}_j$ of finsets of $\mathrm{Fin}\,\mathrm{dim}$ (selectedRows$_j$ the subtype, rows$_j$ the inclusion); a point $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`; $M_k \in \mathbb N$ with $M_k > 0$ (hMk) and an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x` (hgood); a finite type $X_0$ and $\mathrm{stride}_0 : X_0 \to \mathbb N$; a real $P \ge 0$ (hP) with $M_k \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$ for all $j$; finite types $Q_j$; $\mathbb Z$-span of `basis j` equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$ (indexed by $Q_j$) of $\Lambda_j =$ `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, each a $\mathbb Z$-lattice; a natural number $d \ne 0$; $H_0, \mathrm{step}_0 : \mathrm{FullInput} \to \mathbb N$ and $c_0 : \mathrm{FullInput} \to \mathbb Z$ (FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`) with $H_0 > 0$ and each `integerProgressionSupport (c₀ t) (step₀ t) (H₀ t)` contained in $[0,$ `allocatedPrincipalSides B U basis S t`$)$; $\mathrm{modulus} =$ `canonicalSlicedModulus selection stride₀ m x` (with $M = M_k$; hcanonical); a residue label $r_0 : \mathrm{FullInput} \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{modulus}$ whose cell has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀` (hcell); left-invariant probability measures $\nu_j$ on the tori `euclideanSubspace (U j)` $/\Lambda_j$; a left-invariant probability measure $\mu$ on the compact Borel group `CoefficientTorus U` over `LayerSamplerVariables G I n B`, and one $\mu_{\mathrm{rows}}$ on `CoefficientTorus U` over $\mathrm{Fin}\,\mathrm{dim}$; and a finite type $X$ with decidable equality. Let grid be the predicate `allocatedGridAxis U basis S.value`; Tuple the principal tuple index over the non-grid axes, with $H, \mathrm{step}, c$ the restrictions of $H_0, \mathrm{step}_0, c_0$ and $L$ the side lengths `allocatedPrincipalSides` on Tuple; wholeLaw $=$ `containedSupportedProgressionLaw … H₀ step₀ c₀ … hH₀ hsubset₀ modulus r₀ hcell` and gridLaw the corresponding `containedSupportedProgressionAxisLaw … grid`; jetHaar the product of the $\nu_j$ over rows; density $=$ `allocatedCoefficientDensity B U basis hb o hR hσ S`; and cover $=$ `quotientIntegerCover (coefficientIntegerLattice U) d`.
--
--   **Hypotheses.** Reals $D, \mathrm{target}, P_k, P_\rho, F, Q_{\mathrm{stride}}$ with `AllocatedComparisonDimensions B (Fin dim) selectedRows D` ($D \ge 0$ bounds $m$, $|G|$, $\mathrm{dim}$, the numbers of axes, tuples, block parameters, outputs, rows and coefficient exponents, and `probabilityProfileLipschitz`), $P_k, P_\rho, \mathrm{target}, F, Q_{\mathrm{stride}} \ge 0$, $M_k \le e^{P_k}$, $0 < \mathrm{stride}_0(i) \le e^{Q_{\mathrm{stride}}}$, and $\exp(\texttt{allocatedAffineLengthLog m D P Prho Pk target F}\ ((m+1)P_k + |X_0|Q_{\mathrm{stride}})) \le S.\mathrm{value}$. A family $g_y$ (for $y$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S)`) of measurable, nonnegative, jetHaar-integrable functions on `EuclideanJetLayers U selectedRows` such that the image of the measure with density $\mathrm{density}\circ\mathrm{cover}$ with respect to $\mu$ under `euclideanCoefficientJetMap U root_y dirs_y rows` is the measure with density $g_y$ with respect to jetHaar (root$_y$, dirs$_y$ being `allocatedPhysicalCubeRoot B U basis S 0 x y` and `allocatedPhysicalCubeDirections B U basis S x y`). Reals $\delta, \eta$, a map $\rho$ from predicates on axes to $\mathbb R_{\ge 0}$ and a real $t \le 1$ with `AllocatedAffineCoveredComparison B rows δ η ρ t` (OpenAI's uniform comparison statement for affine covered profiles); $0 < \rho(\mathrm{grid}) \le 1$; $\sigma_j \le t$; $\mathrm{step}_j > 0$ on Tuple; $\delta > 0$ with $\delta^{-1} \le e^F$; $\delta L_j \le |\texttt{integerProgressionSupport (c j) (step j) (H j)}|$ on Tuple; $\mathrm{dim} \le m+1$; $|a| \le j+1$ for $a \in \mathrm{rowSets}_j$; a tuple $y_0$ of positive wholeLaw weight; $T : \mathrm{Fin}\,m \to \mathbb R$ with `partitionedIdealRadius (Fin dim) m` $+1 \le T_j$ and $|\texttt{BoundedCoefficientExponent …(j+1)}|\cdot 2^{\mathrm{dim}}(\mathrm{dim}+1)^{j+1} \le T_j$; $C : \mathrm{Fin}\,m \to \mathbb R$ with $C_j \ge 0$, $\|(\texttt{normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)})^{-1}v\| \le C_j\|v\|$ and $C_j(|I_j|+1)T_jR_j \le 1/4$; $\rho(\mathrm{grid})^{-1} \le e^{P_\rho}$; $0 \le \eta \le \exp(-(\mathrm{target} + 1 + D\cdot m2^{m+1}P_k + 4))$; a natural number $\mathrm{period} \ne 0$ equal to `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hgood m)` with $\mathrm{period} \mid d$; $\mathrm{siteRadius} \in \mathbb R_{\ge 0}$ with $1 \le \mathrm{siteRadius}$, $(|\mathrm{rowSets}_j|+1)\cdot 2^{\mathrm{dim}}\cdot C_j(|I_j|+1)\cdot 2\,\mathrm{siteRadius}\,R_j \le 1/4$ and $|\mathrm{rowSets}_j|\,T_j \le \mathrm{siteRadius}$ for all $j$; $C_{\mathrm{fwd}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\texttt{normalizedOrthogonalChart …}\,v\| \le C_{\mathrm{fwd},j}\|v\|$; $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$; reals $P_{\mathrm{box}}, V_{\log}, N_{\log}, M_{\log} \ge 0$ with $2\cdot$`allocatedRowSlicedSiteRadius rowSets` $\le e^{P_{\mathrm{box}}}$, `allocatedFullGridNaturalVolume B U basis S rowSets` $\le e^{V_{\log}}$, $\|$`allocatedProductIdealNormalizer B U basis S rowSets`$^{-1}\| \le e^{N_{\log}}$ and `layerKernelIndexBound m Mk`$^{|\texttt{LayerSamplerAxis I n}|}\cdot$`coefficientDeckPeriodCap selectedRows Q period` $\le e^{M_{\log}}$; and a real $\mathrm{baseAmbient} \ge 0$ with $V_{\log}, N_{\log}, M_{\log}, 2^{\mathrm{dim}}, |\texttt{LayerSamplerAxis I n}|, |\Sigma_a\,\mathrm{selectedRows}_{\mathrm{layer}(a)}| \le \mathrm{baseAmbient}$ and each of $|(\prod_j(\mathbb Z/\mathrm{period})^{\mathrm{Fin}(n_j)})\times(\prod_j(\mathbb Z/\mathrm{period})^{Q_j})|$, $K$, $\sum_j C_{\mathrm{fwd},j}|J_j|$, `normalizedSiteCutoffBound`, $d$, period, $\sum_j|\mathrm{rowSets}_j|$ and $S.\mathrm{value}^{\texttt{layerTailDegree m}+1}$ at most $e^{\mathrm{baseAmbient}}$.
--
--   **Conclusion.** Put ambientQ $=$ `idealSiteLogBudget` $(|\Sigma_a\,\mathrm{selectedRows}_{\mathrm{layer}(a)}|, \mathrm{dim}, P_{\mathrm{box}} + P_\rho + V_{\log} + N_{\log} + M_{\log} + \mathrm{target})$, ambientBudget $=$ `affineAmbientPrimitiveBudget baseAmbient ambientQ`, center $=$ `principalProgressionSliceCenter … L c`, width $=$ `principalProgressionSliceWidth … L H step`, ideal $=$ `diagonalImageDensity (o ↦ R_{layer(o)}) (activeAveragedSlicedProfileIdeal … grid rows (ρ grid) center width)`, and $\mathrm{profile}(y) = \mathrm{gridLaw.mean}\bigl(u \mapsto \texttt{allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows hb o bW d}\ (\texttt{principalAxisJoin grid u}\ (\texttt{principalAxisRestrict (¬ grid) y₀}))\ \mathrm{modulus}\ \mathrm{ideal}\ y\bigr)$. For every natural number $\mathrm{spatialModulus} \ne 0$ equal to period and all $\mathrm{stride}, N : X \to \mathbb N$ with $\mathrm{modulus} =$ refined $:=$ `residueRefinedPeriod spatialModulus stride`, let wholeReference be the constant map with value $y_0$ (on labels $\mathrm{FullInput} \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{refined}$) and $r =$ `principalResidueLabel refined y₀`. Then for all reals $W \ge 0, \tau, \xi_n, \mathrm{mesh}$, $\mathrm{base} : X \to \mathbb Z$, finsets cells of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride`, `VectorPolynomial X ℝ (J j → ℝ)`s $\mathrm{poly}_j$ of degree at most $j+1$ with all coefficients in $U_j$, test from integer cubes $X \to (\mathrm{Unit}\oplus\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z$ to $\mathbb C$ (with point $=$ `physicalCubeRowSample U d rows poly hmem`), model $:$ `EuclideanJetLayers U selectedRows` $\to \mathbb C$, and reals $\kappa$, lossTarget, $P_{\mathrm{ph}}$, $D_{\mathrm{ph}}$, $\varepsilon_{\mathrm{trunc}}$, $P_{\mathrm{sample}}$, $R_{\mathrm{rank}}$, $S_{\mathrm{stride}}$, $\varepsilon_{\mathrm{sample}}$, $\eta_{\mathrm{sample}}$: if
--
--   - $\mathrm{stride} > 0$, $N > 0$, $\tau > 0$, $\mathrm{mesh} > 0$, `allocatedPhysicalRootBudget B U basis S (fun _ => 0)` $\le W$, and $\|\mathrm{test}\| \le 1$;
--   - $\kappa \le \mathrm{Re}$ of the wholeLaw complex mean of `allocatedRecenteredProfileTerm B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test (y z ↦ g y z)` (with $\tau, \xi_n$);
--   - $0 \le \varepsilon_{\mathrm{trunc}}$ and $\|\mathrm{profile}(z) - \mathrm{model}(z)\| \le \varepsilon_{\mathrm{trunc}}$ for all $z$;
--   - $P_{\mathrm{sample}} \ge 0$ bounds $|X|$, $(\mathrm{dim}+1)|X|$, $|\texttt{CoefficientAmbientIndex (Fin dim) J}|$ and ambientBudget; $d$, $S_{\mathrm{stride}}$ (with $0 \le S_{\mathrm{stride}}$), $1/\tau$, $1/\varepsilon_{\mathrm{sample}}$ (with $\varepsilon_{\mathrm{sample}} > 0$), $\eta_{\mathrm{sample}}^{-1}$ (with $\eta_{\mathrm{sample}} > 0$) and $\sum_j|\texttt{BoundedCoefficientExponent (Fin dim) (j+1)}|$ are at most $e^{P_{\mathrm{sample}}}$; and $\mathrm{stride}(i) \le S_{\mathrm{stride}}$;
--   - with $A$ the natural number chosen by `exists_translated_physical_jet_l1_perturbation m dim`: $\exp((P_{\mathrm{sample}} + A)^A) \le N(i)$ for all $i$ and $\le R_{\mathrm{rank}}$, and `HasLayerSamplingRank (j+1) N Rrank (U j) (poly j)` for all $j$;
--   - there is a function actual on the torus `JetAmbientIndex selectedRows J` $\to \mathbb R/\mathbb Z$, $L_a$-Lipschitz and bounded in norm by $C_a$ with $L_a, C_a \le e^{P_{\mathrm{sample}}}$, such that $\mathrm{wholeLaw.mean}(v \mapsto g_v(y)) = \mathrm{actual}(\texttt{coveredJetAmbientTorus U 1 y})$ for all $y$;
--   - with $H_{sp} =$ `trimmedSpatialRootScale τ N stride` and $V =$ `narrowTrimmedSpatialWidths W τ ξn N`: $V > 0$ and $\sum_z$ `selectedResidueSmoothWeight stride cells V z` $> 0$;
--   - for some real $\rho_{\mathrm{ph}}$: $\xi_n \le 1$; $8(1+W)\,\mathrm{stride}(t)\,\rho_{\mathrm{ph}} \le \xi_n\tau N(t)$ for all $t$; $8\cdot$`probabilityProfileLipschitz` $\le \rho_{\mathrm{ph}}$; and $2|\mathrm{Option}(\texttt{LayerSamplerVariables G I n B})|\cdot 2\cdot$`allocatedPhysicalEntryBudget B U basis S (fun _ => 0)` $\le \rho_{\mathrm{ph}}$;
--   - $0 \le P_{\mathrm{ph}}$, $M_k \le e^{P_{\mathrm{ph}}}$, $\mathrm{spatialModulus} \le e^{P_{\mathrm{ph}}^2}$, $\mathrm{dim}+1$, $|G|$, $|X| \le P_{\mathrm{ph}}$, $D_{\mathrm{ph}} \le e^{P_{\mathrm{ph}}}$, and $W \le D_{\mathrm{ph}}S.\mathrm{value}$;
--   - $\mathrm{lossTarget} + $ `coefficientErrorSpatialLog` $P_{\mathrm{ph}} + 8 \le \mathrm{target}$, and $\eta_{\mathrm{sample}}, \varepsilon_{\mathrm{sample}}, \varepsilon_{\mathrm{trunc}} \le e^{-\mathrm{target}}$;
--
--   then
--   $$\kappa - e^{-\mathrm{lossTarget}} \le \mathrm{Re}\sum_{(c', v) \in \mathrm{cells}\times\texttt{spatialWindow}\ H_{sp}\ 4}\texttt{selectedResidueCellWeight stride cells V c'}\cdot\texttt{allocatedRecenteredResidueWeight B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells test r c' v}\cdot\mathrm{model}\bigl(\mathrm{point}(\texttt{allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r c' v})\bigr)$$
--   (the residue weight taken with $\tau$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_constructed_model_source` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedModelSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B162`, `OAIErdos3B200` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedModelSource.lean#L507

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B162
import Definitions.Def_OAIErdos3B200

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
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin dim ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable {X₀ : Type*} [Fintype X₀] (stride₀ : X₀ → ℕ)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows

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
variable (modulus : ℕ)
variable (hcanonical : modulus = canonicalSlicedModulus (M := Mk) selection stride₀ m x)
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin dim) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

variable {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable {X : Type*} [Fintype X] (stride : X → ℕ)
variable (hqcanonical : q = canonicalSlicedModulus (M := Mk) selection stride m x)
variable (hperiodcanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell).weight y₀)

end Erdos3.VectorPolynomial

end

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
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin dim ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable {X₀ : Type*} [Fintype X₀] (stride₀ : X₀ → ℕ)
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
variable (modulus : ℕ)
variable (hcanonical : modulus = canonicalSlicedModulus (M := Mk) selection stride₀ m x)
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
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
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin dim) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

omit [∀ j, Nonempty (rowSets j)] in
include hcanonical μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in
theorem allocatedCanonicalSlice_constructed_model_source
    {D target Pk Prho F Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hQstride : 0 ≤ Qstride)
    (hstride₀ : ∀ i, 0 < stride₀ i) (hstrideBound : ∀ i, (stride₀ i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card X₀ * Qstride)) ≤ S.value)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) jetHaar)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure jetHaar (g y))
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hq : Fintype.card (Fin dim) ≤ m + 1)
    (hrowDegree : ∀ j (a : rowSets j), a.val.card ≤ j.val + 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S))
    (hy₀ : 0 < (wholeLaw).weight y₀)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (period : ℕ) [NeZero period]
    (hperiodCanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m))
    (hdiv : period ∣ d) (siteRadius : ℝ≥0) (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ))
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (hPbox : 0 ≤ Pbox) (hVlog : 0 ≤ Vlog) (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (hmask : (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap selectedRows Q period ≤ Real.exp Mlog)
    (hbaseAmbient : 0 ≤ baseAmbient)
    (hvbase : Vlog ≤ baseAmbient) (hnbase : Nlog ≤ baseAmbient) (hmbase : Mlog ≤ baseAmbient)
    (hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤ Real.exp baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hdbase : (d : ℝ) ≤ Real.exp baseAmbient) (hpbase : (period : ℝ) ≤ Real.exp baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient) :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin dim))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    let center := principalProgressionSliceCenter (α := (Fin dim)) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := (Fin dim)) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option (Fin dim))
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let profile := fun y => ((gridLaw).mean (fun u =>
      allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) modulus ideal y) : ℂ)
    ∀ (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ),
    spatialModulus = period →
    let refined := residueRefinedPeriod spatialModulus stride
    modulus = refined →
    let labels := PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined
    let wholeReference : labels → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
        (allocatedPrincipalSides B U basis S) := fun _ => y₀
    let r := principalResidueLabel refined y₀

    ∀ {W τ ξn mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ),
    let point := physicalCubeRowSample U d rows poly hmem
    ∀ (model : EuclideanJetLayers U selectedRows → ℂ)
      {κ lossTarget Pphysical Dphysical εtrunc Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → 0 < τ → 0 < mesh →
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    (∀ v, ‖test v‖ ≤ 1) →
    κ ≤ ((wholeLaw).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξn)
      B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test
      (fun y z => (g y z : ℂ)))).re →
    0 ≤ εtrunc → (∀ z, ‖profile z - model z‖ ≤ εtrunc) →
    0 ≤ Psample → (Fintype.card X : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Psample →
    (d : ℝ) ≤ Real.exp Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,0} m dim)
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    ∀ (actual : (JetAmbientIndex selectedRows J → UnitAddCircle) → ℂ)
      (La Ca : ℝ≥0),
    LipschitzWith La actual → (∀ z, ‖actual z‖ ≤ Ca) →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Psample →
    (La : ℝ) ≤ Real.exp Psample → (Ca : ℝ) ≤ Real.exp Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    (∀ y, ((wholeLaw).mean (fun v => g v y) : ℂ) = actual (coveredJetAmbientTorus U 1 y)) →
    let _root := allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (wholeReference r)
    let _dirs := allocatedPhysicalCubeDirections B U basis S x (wholeReference r)
    let Hsp := trimmedSpatialRootScale τ N stride
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    let _Csp := ((spatialModulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (Mk : ℝ))) ^ Fintype.card X
    let _volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight stride cells V z) →
    ∀ {ρphysical : ℝ}, ξn ≤ 1 →
    (∀ t, 8 * (1 + W) * (stride t : ℝ) * ρphysical ≤ (ξn * τ) * (N t : ℝ)) →
    8 * (probabilityProfileLipschitz : ℝ) ≤ ρphysical →
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S (fun _ => 0))) ≤ ρphysical →
    0 ≤ Pphysical → (Mk : ℝ) ≤ Real.exp Pphysical →
    (spatialModulus : ℝ) ≤ Real.exp (Pphysical ^ 2) →
    ((dim + 1 : ℕ) : ℝ) ≤ Pphysical → (Fintype.card G : ℝ) ≤ Pphysical →
    (Fintype.card X : ℝ) ≤ Pphysical → Dphysical ≤ Real.exp Pphysical →
    W ≤ Dphysical * S.value →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) → εtrunc ≤ Real.exp (-target) →
    κ - Real.exp (-lossTarget) ≤
      (∑ t : cells × spatialWindow (α := Fin dim) Hsp 4, (selectedResidueCellWeight stride cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U basis S X spatialModulus stride wholeReference x hMk selection hgood
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r
          t.1.val t.2.val))).re := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
