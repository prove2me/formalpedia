-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedDetected_spatial_native_source_sharedWidth
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedDetected_spatial_native_source_sharedWidth
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:49:49.578306+00:00
-- url     : https://prove2.me/theorems/1e8ec17b-c0c1-42f9-a850-7fa4808e142a
-- title:
--   A detected niltest slice gives a twisted native correlation, with a shared spatial width
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ (in `Type`) with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$, $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L_S = $ `S.value`; natural numbers $s$ and $n_X$, with row sets $\mathrm{rowSets}_j = $ `boundedBooleanJetRows (Fin (s+1)) (j+1)`, row types $\mathrm{selectedRows}_j$ and inclusions $\mathrm{rows}_j$; grid is the predicate `allocatedGridAxis U basis L_S` on axes; an embedding $\mathrm{selection} : \mathrm{Fin}(s+1) \hookrightarrow G$; $\mathrm{stride}, N : \mathrm{Fin}\,n_X \to \mathbb N$ with every $N_i \neq 0$; a polynomial $P_{\mathrm{detect}} \in \mathbb N[t]$ and reals $p_{\mathrm{detect}}, q_{\mathrm{detect}}, \alpha$; write $\kappa = |\texttt{LayerSamplerVariables G I n B}|$, $\mathrm{gain} = $ `allocatedDetectedGain s κ Pdetect pDetect qDetect α` $= e^{-((5p_{\mathrm{detect}}+20)\kappa + p_{\mathrm{detect}} + 2)}\,\frac{\alpha}{2}\,\bigl(e^{-(q_{\mathrm{detect}} + C_s)^{C_s}}\bigr)^{2^{s+1}}$ with $C_s = $ `sampledSupportedSlicedDetectionConstant s Pdetect`, and $M_k = $ `allocatedDetectedKernelCutoff s G κ Pdetect pDetect qDetect α` $=$ `scalarKernelCutoff (Fin (s+1)) G 1 ⌈exp(pDetect+1)⌉ (gain/2)` (a natural number); a real $P \ge 0$ with $M_k \le e^{P}$, $R_j \le e^{P}$, $R_j^{-1} \le e^{P}$, $\sigma_j^{-1} \le e^{P}$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^{P}$; finite types $Q_j$; $hb$: the $\mathbb Z$-span of $\mathrm{basis}_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $Q_j$; the assumption that each $\mathbb Z^{J_j} \cap V_j$ is a full lattice in $V_j$; additively left-invariant probability measures $\nu_j$ on $V_j/(\mathbb Z^{J_j} \cap V_j)$; compact Borel structures on `CoefficientTorus (LayerSamplerVariables G I n B) U` and `CoefficientTorus (Fin (s+1)) U` with additively left-invariant probability measures $\mu$, $\mu_{\mathrm{rows}}$; and a Borel structure on `SiteTorus (Finset (Fin (s+1))) U`. All of $hb, o, bW, \mu, \nu, \mu_{\mathrm{rows}}$, $R > 0$, $\sigma > 0$ and the bounds involving $P$ are hypotheses of the theorem.
--
--   Explicit hypotheses (first group): $s \le m$; reals $D, \mathrm{target}, P_k, P_\rho, Q_{\mathrm{stride}}$ with `AllocatedComparisonDimensions B (Fin (s+1)) selectedRows D`, $P_k \ge 0$, $M_k \le e^{P_k}$, $P_\rho, \mathrm{target}, Q_{\mathrm{stride}} \ge 0$, $\mathrm{stride}_i > 0$, $\mathrm{stride}_i \le e^{Q_{\mathrm{stride}}}$, $\exp(\texttt{allocatedAffineLengthLog m D P Prho Pk target (pDetect+1)}((m+1)P_k + n_X Q_{\mathrm{stride}})) \le L_S$; a real $\eta$, $\rho$ assigning to predicates on axes elements of $\mathbb R_{\ge 0}$, and $t \le 1$ with `AllocatedAffineCoveredComparison B rows (exp(-(pDetect+1))) η ρ t htone` (universe levels $0, 0$), $0 < \rho(\mathrm{grid}) \le 1$, $\sigma_j \le t$; $T$ with `partitionedIdealRadius (Fin (s+1)) m` $+1 \le T_j$ and $|\texttt{BoundedCoefficientExponent}\dots(j+1)|\cdot 2^{s+1}(s+2)^{j+1} \le T_j$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ \mathrm{basis}_j)^{-1}v\| \le C_j\|v\|$ and $C_j(|I_j|+1)T_jR_j \le 1/4$; $\rho(\mathrm{grid})^{-1} \le e^{P_\rho}$; $0 \le \eta \le \exp(-(\mathrm{target} + 1 + D\,m2^{m+1}P_k + 4))$; $\mathrm{siteRadius} \ge 1$ with $(|\mathrm{rowSets}_j|+1)\,|\mathcal P(\mathrm{Fin}(s+1))|\,C_j(|I_j|+1)\,2\,\mathrm{siteRadius}\,R_j \le 1/4$; $C_{\mathrm{forward}}$ with $\|\texttt{normalizedOrthogonalChart}\ V_j\ \mathrm{basis}_j\ v\| \le C_{\mathrm{forward}}(j)\|v\|$; $K \ge R_j^{-1}$; $|\mathrm{rowSets}_j|\,T_j \le \mathrm{siteRadius}$; reals $P_{\mathrm{box}}, V_{\log}, N_{\log}, M_{\log}, \mathrm{baseAmbient} \ge 0$ with $2\,$`allocatedRowSlicedSiteRadius rowSets` $\le e^{P_{\mathrm{box}}}$, `allocatedFullGridNaturalVolume B U basis S rowSets` $\le e^{V_{\log}}$, $\|(\texttt{allocatedProductIdealNormalizer B U basis S rowSets})^{-1}\| \le e^{N_{\log}}$, $|\texttt{LayerSamplerAxis I n}|\,m2^{m+1}P_k + \sum_j |Q_j|\,|\mathrm{selectedRows}_j|\,(m+1)P_k \le M_{\log}$, $V_{\log}, N_{\log}, M_{\log}, |\mathcal P(\mathrm{Fin}(s+1))|, |\texttt{LayerSamplerAxis I n}| \le \mathrm{baseAmbient}$, $\sum_j n_j(m+1)P_k + \sum_j |Q_j|(m+1)P_k \le \mathrm{baseAmbient}$, $K, \sum_j C_{\mathrm{forward}}(j)|J_j|, \texttt{normalizedSiteCutoffBound} \le e^{\mathrm{baseAmbient}}$, $(m+1)P_k \le \mathrm{baseAmbient}$, $\sum_j|\mathrm{rowSets}_j| \le e^{\mathrm{baseAmbient}}$, $|\Sigma_a\,\mathrm{selectedRows}_{a.1}| \le \mathrm{baseAmbient}$, $L_S^{\texttt{layerTailDegree}\ m+1} \le e^{\mathrm{baseAmbient}}$; $Q_{\mathrm{grid}} \ge 8(|\texttt{layerIntegerPrincipalSlots B (allocatedGridIntegerAxis B U basis S a)}|+1)$ for grid axes $a$; $A_g$ a Lipschitz constant of `Real.smoothTransition`; the block-count bounds `positiveModerateSpectrumBlockCount j |rowSets j| ((layerTailDegree m + 1)|rowSets j|)` $\le |B_{(j,\mathrm{inr}\,i)}|$ and `uniformSpectrumBlockCount j |rowSets j| ((j+1)|rowSets j|)` $\le |B_{(j,\mathrm{inr}\,i)}|$; reals $D_g, v_g, w_g \ge 0$ with $s+1, j+1, |\mathrm{rowSets}_j|, \texttt{layerTailDegree}\ m+1, |B_{(j,\mathrm{inr}\,i)}|, \#\text{grid axes}, |\texttt{LayerSamplerAxis I n}|, |\Sigma_a\,\mathrm{selectedRows}_{a.1}|, \sum_j|J_j|, \texttt{probabilityProfileLipschitz} \le D_g$, $R_j, R_j^{-1}, |\texttt{BoundedCoefficientExponent}\dots(j+1)| \le e^{v_g}$, $p_{\mathrm{detect}} + 1 \le w_g$; $B_{\mathrm{analytic}} \ge D_g \ge 0$ with `normalizedSiteCutoffBound`, $K\sum_j C_{\mathrm{forward}}(j)|J_j|$, $Q_{\mathrm{grid}} \le e^{B_{\mathrm{analytic}}}$; $P_{\mathrm{num}} \ge 0$ with $|I_j|, n_j, |\texttt{BoundedCoefficientExponent}\dots(j+1)| \le P_{\mathrm{num}}$, $R_j^{-1} \le e^{P_{\mathrm{num}}}$, `mixedDensityCovolumeRatio V_j basis_j` $\le e^{P_{\mathrm{num}}}$; and reals $P_{\mathrm{proj}}, \mathrm{coarseTarget}, E_{\mathrm{coarse}}, p_{\mathrm{Gain}}$.
--
--   Conclusion. Put $\mathrm{ambientQ} = $ `idealSiteLogBudget (card (Σ a, selectedRows a.1)) (s+1) (Pbox + Prho + Vlog + Nlog + Mlog + target)`, $\mathrm{ambientBudget} = $ `affineAmbientPrimitiveBudget baseAmbient ambientQ` and $W = $ `allocatedPhysicalRootBudget B U basis S 0` ($\ge 0$). For all reals $\tau, P_{\mathrm{physical}}$ and $\xi_n > 0$ with $\xi_n \le$ `normalizedTupleNarrowWidth (Fin nX) (tuple index) selection Mk Pphysical coarseTarget`, every finite set $\mathrm{cells}$ of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride`, all vector polynomials $\mathrm{poly}_j \in$ `VectorPolynomial (Fin nX) ℝ (J j → ℝ)` of total degree at most $j+1$ with coefficients in $U_j$, every signal $\phi : \mathbb Z^{n_X} \to \mathbb C$ with $\|\phi\| \le 1$ on `integerBox N` and $\phi = 0$ outside it, all reals $\mathrm{lossTarget}, P_{\mathrm{sample}}, R_{\mathrm{rank}}, S_{\mathrm{stride}}, \varepsilon_{\mathrm{sample}}, \eta_{\mathrm{sample}}, P_{\mathrm{native}}, P_{\mathrm{side}}$, and all $C_{\mathrm{proj}}, V_{\mathrm{proj}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$, assume:
--
--   - $\mathrm{stride}_i > 0$, $N_i > 0$, $\tau > 0$; $P_{\mathrm{sample}} \ge 0$, $n_X, |\mathrm{Option}(\mathrm{Fin}(s+1)) \times \mathrm{Fin}\,n_X| \le P_{\mathrm{sample}}$, $0 \le S_{\mathrm{stride}} \le e^{P_{\mathrm{sample}}}$, $\varepsilon_{\mathrm{sample}} > 0$, $1/\tau, 1/\varepsilon_{\mathrm{sample}} \le e^{P_{\mathrm{sample}}}$, $\mathrm{stride}_i \le S_{\mathrm{stride}}$; with $A$ chosen by `exists_translated_physical_jet_l1_perturbation m (s+1)`, $\exp((P_{\mathrm{sample}}+A)^A) \le N_i$, `HasLayerSamplingRank (j+1) N R_rank (U j) (poly j)`, $\exp((P_{\mathrm{sample}}+A)^A) \le R_{\mathrm{rank}}$; $\eta_{\mathrm{sample}} > 0$, $|\texttt{CoefficientAmbientIndex (Fin (s+1)) J}| \le P_{\mathrm{sample}}$, $\mathrm{ambientBudget} \le P_{\mathrm{sample}}$, $\sum_j|\texttt{BoundedCoefficientExponent (Fin (s+1)) (j+1)}| \le e^{P_{\mathrm{sample}}}$, $\eta_{\mathrm{sample}}^{-1} \le e^{P_{\mathrm{sample}}}$;
--   - $P_{\mathrm{physical}} \ge 0$, $M_k \le e^{P_{\mathrm{physical}}}$, $m+1, s+2, |G|, n_X \le P_{\mathrm{physical}}$, $\mathrm{coarseTarget} \ge 0$, $\mathrm{lossTarget} + $ `coefficientErrorSpatialLog Pphysical` $+ 8 \le \mathrm{target}$, $\eta_{\mathrm{sample}}, \varepsilon_{\mathrm{sample}} \le e^{-\mathrm{target}}$;
--   - with $A_{\mathrm{mass}}, A_{\mathrm{analytic}}$ chosen by `exists_allocatedAffineModelMass_budget m (s+1)` and `exists_allocatedAffineAnalytic_budget m (s+1)`, $F_{\mathrm{model}} = m2^{s+1}(P_{\mathrm{num}}+8)(1+4P_{\mathrm{num}}) + |\texttt{LayerSamplerAxis I n}|\,m2^{m+1}P_k + \sum_j|Q_j|\,|\mathrm{selectedRows}_j|\,(m+1)P_k$, $C_{\mathrm{grid}}$ chosen by `exists_preparedModularCanonicalDetector_grid_parameters m (s+1) Ag`, $Q_{\log} = (m+1)P_k + n_X Q_{\mathrm{stride}}$, $t_g = s + 1 + Q_{\log} + p_{\mathrm{detect}} + 2$, $p_g = C_{\mathrm{grid}} + (s+2)Q_{\log} + p_{\mathrm{detect}} + 5$ and $p = $ `slicedGridGeometryLog Dg vg wg tg` $+ p_g$: $P_{\mathrm{native}} \ge 0$ and $D_g, p, v_g, F_{\mathrm{model}}, P_\rho, P_k, \mathrm{target}, B_{\mathrm{analytic}}, P_{\mathrm{physical}}, E_{\mathrm{coarse}}, p_{\mathrm{Gain}} \in [0, P_{\mathrm{native}}]$;
--   - $\mathrm{stride}_i, 1/\tau \le e^{P_{\mathrm{physical}}}$; $e^{-p_{\mathrm{Gain}}}/2 \le \mathrm{gain}/2$; $p_{\mathrm{Gain}} + 32 \le P_{\mathrm{proj}}, \mathrm{coarseTarget}, E_{\mathrm{coarse}}, \mathrm{lossTarget}$;
--   - with $A_{\mathrm{cover}}, A_{\mathrm{proj}}$ the two natural numbers chosen by `exists_allocated_canonical_constructed_projection m (s+1)`, $\mathrm{coverLog} = (P_{\mathrm{proj}} + s + 3 + A_{\mathrm{cover}})^{A_{\mathrm{cover}}}$, $A_{\mathrm{sample}}$ chosen by `exists_allocatedCanonicalProjection_composed_budget m (s+1) A_cover` and $P_{\mathrm{mass}} = (P_{\mathrm{proj}} + A_{\mathrm{sample}})^{A_{\mathrm{sample}}}$: $\mathrm{coverLog} \le \mathrm{baseAmbient}$, $\mathrm{coverLog}, P_{\mathrm{mass}} \le P_{\mathrm{sample}}$; $\|\texttt{normalizedOrthogonalChart}\ V_j\ \mathrm{basis}_j\ z\| \le C_{\mathrm{proj}}(j)\|z\|$; $0 \le$ `mixedDensityCovolumeRatio V_j basis_j` $\le V_{\mathrm{proj}}(j)$; $\sigma_j \le 1$; $C_j(|I_j|+1)R_j \le 1/4$; $n_X, |\mathrm{Option}(\mathrm{Fin}(s+1)) \times \mathrm{Fin}\,n_X| \le P_{\mathrm{mass}}$; $\mathrm{stride}_i, 1/\tau \le e^{P_{\mathrm{mass}}}$; with $A_w$ chosen by `exists_translated_physical_jet_density_window_mass m (s+1)`, $\exp((P_{\mathrm{mass}}+A_w)^{A_w}) \le N_i$ and $\le R_{\mathrm{rank}}$; $|\texttt{CoefficientAmbientIndex (Fin (s+1)) J}| \le P_{\mathrm{mass}}$; $\sum_j|\texttt{BoundedCoefficientExponent (Fin (s+1)) (j+1)}| \le e^{P_{\mathrm{mass}}}$; $\kappa \le e^{P_{\mathrm{physical}}}$;
--   - $1 \le P_{\mathrm{proj}}$; $m, |G|, \kappa, n_X, |\mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times \mathrm{Fin}\,n_X|, |\texttt{BoundedCoefficientExponent}\dots(j+1)|, |I_j|, n_j, |J_j| \le P_{\mathrm{proj}}$; $(m+1)P_k \le P_{\mathrm{proj}}$; $L_S, W, R_j^{-1}, \sigma_j^{-1}, \texttt{probabilityProfileLipschitz}, C_{\mathrm{proj}}(j), V_{\mathrm{proj}}(j), \mathrm{stride}_i, \tau^{-1}, \xi_n^{-1} \le e^{P_{\mathrm{proj}}}$; $\exp((P_{\mathrm{proj}} + A_{\mathrm{proj}})^{A_{\mathrm{proj}}}) \le N_i$ and $\le R_{\mathrm{rank}}$;
--   - $P_{\mathrm{proj}}, P_{\mathrm{mass}}, P_{\mathrm{physical}}, \mathrm{coarseTarget} \le P_{\mathrm{side}}$, and with $A_c$ chosen by `exists_allocatedCanonicalSpatial_cutoff m`, $\exp((P_{\mathrm{side}} + A_c)^{A_c} + P_{\mathrm{proj}}) \le N_i$;
--   - $\mathrm{cells}$ is nonempty; $\mathrm{bases} \subseteq \mathbb Z^{n_X}$ is a nonempty finite set; with $\mathcal V = $ `narrowTrimmedSpatialWidths W τ ξn N`, $hmass$: $\sum_z$ `selectedResidueSmoothWeight stride cells 𝒱 z` $> 0$, and $htotal$: `selectedJointDensityMass bases stride cells 𝒱 (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)` $> 0$; let Path $= \mathrm{bases} \times$ `rectangularWeightIndices 0 𝒱 1` and pathLaw $=$ `allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N _ hW hτ hξn stride cells hmass bases hbases htotal` (a finite probability law on Path);
--   - for a nonempty finite type $T_{\mathrm{detect}}$ with an injection $e : T_{\mathrm{detect}} \to (\texttt{LayerSamplerVariables G I n B} \to \mathbb Z)$; for each $z \in$ Path a nonempty type $\mathrm{Tests}_z$, and for $j \in \mathrm{Tests}_z$ a Lie algebra over $\mathbb Q$ with Hausdorff topological-vector-space structure on its real base change, a natural number $\mathrm{dims}_{z,j}$, a `RationalFilteredNilmanifold` $D_{z,j}$ of degree $s$ and a niltest $V_{z,j}$ on it (variables `LayerSamplerVariables G I n B`, weights $1$), finite sets $\mathrm{slices}_{z,j} \subseteq T_{\mathrm{detect}}$, $c_{z,j}$, $\mathrm{step}_{z,j} > 0$, $H_{z,j}$ with $e(\mathrm{slices}_{z,j}) = $ `commonStrideBox (c z j) (step z j) (H z j)`; $p_{\mathrm{detect}}, q_{\mathrm{detect}} \ge 0$; each $e(\mathrm{slices}_{z,j})$ is `IsDenseCommonStrideBox` for the sides ($L_S$ on $G$, `allocatedPrincipalSides B U basis S` on tuple indices) and $p_{\mathrm{detect}}$; $\kappa \le P_{\mathrm{detect}}(q_{\mathrm{detect}})$; each $V_{z,j}$ has complexity $\le P_{\mathrm{detect}}(q_{\mathrm{detect}})$ and norm bound $\le 1$; $0 < \alpha \le 1$; $\kappa\,e^{-p_{\mathrm{detect}}} \le \alpha/8$; $e^{-q_{\mathrm{detect}}} \le \alpha/4$; $\alpha \le$ `sampledSliceSeminorm pathLaw (fun z t => jointIntegerPhysicalSite (e t) z) slices (fun z j t => conj (V z j (commonStrideIndex (c z j) (step z j) (e t))))` $(\phi)$; $(s+1)(s+3) \le |G|$; and $M_k \le L_S$.
--
--   Then, with $C$ chosen by `exists_canonicalSlicedNative_input_budget m (s+1) A_mass A_analytic`, $B_{\mathrm{budget}} = (P_{\mathrm{native}} + C)^C$, $A_{\mathrm{norm}}$ chosen by `exists_allocatedRecenteredFactor_normalization m (s+1)`, $A_{\mathrm{native}}$ chosen by `exists_native_partner_of_physical_cube_mixture_all_degrees s`, $A'$ chosen by `exists_normalizedNative_uniform_budget m A_norm A_native` (all existence theorems of OpenAI) and $\mathrm{budget} = (B_{\mathrm{budget}} + A')^{A'}$, there exist twistData : `NormalizedPolynomialTwist (Fin nX) (Σ j, J j) (exp budget) (exp budget) (exp budget)` (a modulus and a cover, positive and at most $e^{\mathrm{budget}}$, a residue mask of norm $\le 1$ and an $e^{\mathrm{budget}}$-Lipschitz smooth factor of norm $\le 1$) and $F_{\mathrm{native}} : $ `integerBox N` $\to \mathbb C$ such that `NativeSampleModel (fun _ => 1) s budget (fun u => u) Fnative` is nonempty ($F_{\mathrm{native}}$ is the evaluation of a niltest of norm bound $\le 1$ and complexity $\le \mathrm{budget}$ on a rational filtered nilmanifold of degree $s$) and
--   $$e^{-\mathrm{budget}} \le \Bigl\|\mathbb E_{u \in \texttt{integerBox N}}\ \phi(u)\,\overline{\overline{\texttt{twistData.eval N poly}(u)}\,F_{\mathrm{native}}(u)}\Bigr\|.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedDetected_spatial_native_source_sharedWidth` in `lean/OAI/Combinatorics/Progressions/Geometry/SharedWidthAllocatedDetectedSpatialNativeSourceGeneral.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B178`, `OAIErdos3B199`, `OAIErdos3B1323`, `OAIErdos3B1327` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/SharedWidthAllocatedDetectedSpatialNativeSourceGeneral.lean#L525

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B178
import Definitions.Def_OAIErdos3B199
import Definitions.Def_OAIErdos3B1323
import Definitions.Def_OAIErdos3B1327

namespace OAI

section

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
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

end Erdos3.VectorPolynomial

end

section

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
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

include hb o bW μ ν μrows hR hσ hP hMkP hRP hRi hσi hcount in
theorem exists_allocatedDetected_spatial_native_source_sharedWidth
    (hsm : s ≤ m)
    {D target Pk Prho Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hPk : 0 ≤ Pk)
    (hMkPk : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho)
    (htarget : 0 ≤ target)
    (hQstride : 0 ≤ Qstride)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1) (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    {η : ℝ}
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (t : ℝ)
    (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{0, 0, _, _, _, _, _} (G := G) B rows (Real.exp (-(pDetect + 1))) η ρ t htone)
    (hρ : 0 < ρ grid)
    (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (T : Fin m → ℝ)
    (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) * ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ)
    (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (siteRadius : ℝ≥0)
    (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0)
    (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ))
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (hPbox : 0 ≤ Pbox)
    (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog)
    (hMlog : 0 ≤ Mlog)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (hmaskLog : (Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * (((m + 1 : ℕ) : ℝ) * Pk)) ≤ Mlog)
    (hbaseAmbient : 0 ≤ baseAmbient)
    (hvbase : Vlog ≤ baseAmbient)
    (hnbase : Nlog ≤ baseAmbient)
    (hmbase : Mlog ≤ baseAmbient)
    (hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabelLog : (∑ j, (n j : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk)) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk) ≤ baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hperiodLog : ((m + 1 : ℕ) : ℝ) * Pk ≤ baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0)
    (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg : ℝ}
    (hDg : 0 ≤ Dg)
    (hvg : 0 ≤ vg)
    (hwg : 0 ≤ wg)
    (hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg)
    (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg)
    (hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : pDetect + 1 ≤ wg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ}
    (hBanalytic : 0 ≤ Banalytic)
    (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ}
    (hPnum : 0 ≤ Pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum)
    (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {Pproj coarseTarget Ecoarse pGain : ℝ}
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {τ Pphysical : ℝ},
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn), ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (signal : ((Fin nX) → ℤ) → ℂ),
    (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    ∀ {lossTarget Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → (hτSpatial : 0 < τ) →
    0 ≤ Psample → (Fintype.card (Fin nX) : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin (s + 1)) × (Fin nX)) : ℝ) ≤ Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,0,0} m (s + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (hPhysicalNonneg : 0 ≤ Pphysical) → (hMkPhysicalBound : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pphysical) →
    (hmPhysicalBound : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) → (hCoarseNonneg : 0 ≤ coarseTarget) →
    (hDimPhysicalBound : (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical) →
    (hGPhysicalBound : (Fintype.card G : ℝ) ≤ Pphysical) →
    (hXPhysicalBound : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical) →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let Cgrid := Classical.choose (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (s + 1) Ag)
    let Qlog := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let tg := ((s + 1 : ℕ) : ℝ) + Qlog + (pDetect + 1) + 1
    let pg := (Cgrid : ℝ) + (((s + 1) + 1 : ℕ) : ℝ) * Qlog + (pDetect + 1) + 4
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ (allocatedDetectedGain s (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) / 2 →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    ∀ (Cproj Vproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1))
    let coverLog := (Pproj + ((s + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (s + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vproj j) →
    (∀ j, σ j ≤ 1) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmass →
    (Fintype.card (Option (Fin (s + 1)) × Fin nX) : ℝ) ≤ Pmass →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pmass) → 1 / τ ≤ Real.exp Pmass →
    let AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,0,0,max 0 0 0} m (s + 1))
    (∀ i, Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ (N i : ℝ)) →
    Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ Rrank →
    (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Pmass →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Pphysical →
    1 ≤ Pproj → (m : ℝ) ≤ Pproj →
    (Fintype.card G : ℝ) ≤ Pproj → (S.value : ℝ) ≤ Real.exp Pproj →
    ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj → W ≤ Real.exp Pproj →
    (∀ j, (R j)⁻¹ ≤ Real.exp Pproj) → (∀ j, (σ j)⁻¹ ≤ Real.exp Pproj) →
    (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) → (∀ j, (n j : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj) →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj →
    (∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) → (∀ j, (Vproj j : ℝ) ≤ Real.exp Pproj) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pproj →
    (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pproj) → τ⁻¹ ≤ Real.exp Pproj → ξn⁻¹ ≤ Real.exp Pproj →
    let Aproj := Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1)))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
    ∀ {Pside : ℝ}, Pproj ≤ Pside → Pmass ≤ Pside →
    Pphysical ≤ Pside → coarseTarget ≤ Pside →
    (∀ i, Real.exp ((Pside + Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m)) ^
      Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m) + Pproj) ≤ (N i : ℝ)) →
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), (hbases : bases.Nonempty) →
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    (htotal : 0 < selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)) →
    let Path := bases × rectangularWeightIndices 0 V 1
    let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N
      (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW hτSpatial hξn stride cells hmass bases hbases htotal
    ∀ {Tdetect : Type} [Fintype Tdetect] [Nonempty Tdetect]
      (e : Tdetect → LayerSamplerVariables G I n B → ℤ), Function.Injective e →
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Tdetect)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    0 ≤ pDetect → 0 ≤ qDetect →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pDetect ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    0 < α → α ≤ 1 →
    Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-pDetect) ≤ α / 8 →
    Real.exp (-qDetect) ≤ α / 4 →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    (s + 1) * (s + 3) ≤ Fintype.card G → (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) ≤ S.value →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{0,0,0,0,0,0} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖ := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
