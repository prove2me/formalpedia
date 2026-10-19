-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_spatial_native_source_sharedWidth_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_spatial_native_source_sharedWidth_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:17:25.618157+00:00
-- url     : https://prove2.me/theorems/799d5245-aa8f-483b-846a-ef23f1e69f0a
-- title:
--   A large allocated sliced tuple value forces a correlation of the signal with a bounded twist times a native sample model
-- statement:
--   This statement lives in a large context of data and structures defined by OpenAI, followed by a long list of numerical hypotheses; we follow the Lean declarations in order. Several constants are natural numbers chosen by OpenAI (with `Classical.choose`) from existence lemmas; we name them by their lemma.
--
--   **Context.** Fix a natural number $m$; a finite type $G$ with decidable equality; for each $j < m$ a finite type $I_j$, a natural number $n_j$, a finite type $J_j$, a real subspace $U_j$ of $\mathbb{R}^{J_j}$ with Euclidean subspace $V_j$, and a real basis $\mathrm{basis}_j$ of $V_j^{\perp}$ indexed by $\{0,\dots,n_j-1\}$ whose $\mathbb{Z}$-span is OpenAI's projected integer lattice of $V_j$; finite types $B_a$ for the layer sampler axes $a$ (OpenAI's `LayerSamplerAxis I n`; the axis $(j, c)$ has degree $j+1$); reals $R_j > 0$, $\sigma_j > 0$; a layer sampler scale $S$ (main field `S.value`); natural numbers $s$ and $n_X$. Let $\mathcal{S} = \{0,\dots,s\}$ and, for $j < m$, let $\mathrm{rowSets}_j$ = `boundedBooleanJetRows (Fin (s+1)) (j+1)` (a finite set of subsets of $\mathcal{S}$, OpenAI). Fix $x : G \to$ `IntegerScalarCubeBox (Fin (s+1)) S.value`, a natural number $M_k > 0$, an embedding $\mathrm{selection} : \mathcal{S} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/M_k) M_k x` (OpenAI; see the statement on the good kernel uniform candidate); a nonzero natural number $\mathrm{period}$ equal to `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hgood m)`; $\mathrm{stride}, N : \{0,\dots,n_X-1\} \to \mathbb{N}$ with all $N_i \ne 0$; $\mathrm{modulus} = $ `residueRefinedPeriod period stride` $= \mathrm{period}\cdot\prod_i \mathrm{stride}_i$; a real $P \ge 0$ with $M_k \le e^{P}$, $R_j \le e^{P}$, $R_j^{-1} \le e^{P}$, $\sigma_j^{-1} \le e^{P}$, and (number of exponent vectors of total degree at most $j+1$ in the layer sampler variables) $+ 1 \le e^{P}$, for all $j$. Let `grid` = `allocatedGridAxis U basis S.value` (OpenAI), $\mathrm{Tuple}$ the principal indices $(a, b, v)$ with $a$ a non-grid axis, and $L$ the side lengths `allocatedPrincipalSides B U basis S` restricted to them. Fix finite types $Q_j$, orthonormal bases $o_j$ of $V_j$, $\mathbb{Z}$-bases $bW_j$ (indexed by $Q_j$) of the lattice sections $\Lambda_j = \mathbb{Z}^{J_j} \cap V_j$ (assumed $\mathbb{Z}$-lattices); functions $H_0, \mathrm{step}_0 : (\text{principal indices}) \to \mathbb{N}$ and $c_0$ to $\mathbb{Z}$ with $H_0 > 0$ and each progression $\{c_0 + \mathrm{step}_0 k : k < H_0\}$ inside $\{0, \dots, \mathrm{side} - 1\}$; residues $r_0$ modulo $\mathrm{modulus}$ such that the residue cell has positive mass under OpenAI's principal tuple weights with lengths $H_0$; and write $H$, $\mathrm{step}$, $c$ for their restrictions to $\mathrm{Tuple}$ and `wholeLaw` for OpenAI's `containedSupportedProgressionLaw` built from these data. Fix left-invariant probability measures $\nu_j$ on $V_j/\Lambda_j$, a left-invariant Borel probability measure $\mu$ on the compact coefficient torus of the layer sampler variables, and one, $\mu_{\mathrm{rows}}$, on the compact coefficient torus of $\mathcal{S}$ (OpenAI's `CoefficientTorus`); the site torus of the subsets of $\mathcal{S}$ carries a Borel structure.
--
--   **First group of hypotheses.** Reals $D, \mathrm{target}, P_k, P_\rho, F, Q_{\mathrm{stride}}$ with `AllocatedComparisonDimensions B (Fin (s+1)) selectedRows D` (OpenAI), $P_k, P_\rho, \mathrm{target}, F, Q_{\mathrm{stride}} \ge 0$, $M_k \le e^{P_k}$, $0 < \mathrm{stride}_i \le e^{Q_{\mathrm{stride}}}$ for all $i$, and $\exp\bigl(\texttt{allocatedAffineLengthLog}\ m\ D\ P\ P_\rho\ P_k\ \mathrm{target}\ F\ ((m+1)P_k + n_X Q_{\mathrm{stride}})\bigr) \le$ `S.value`. Reals $\delta, \eta$, a function $\rho$ from predicates on axes to $\mathbb{R}_{\ge 0}$, and a real $t \le 1$ with `AllocatedAffineCoveredComparison B rows δ η ρ t` (OpenAI), $0 < \rho(\mathrm{grid}) \le 1$, $\sigma_j \le t$ for all $j$, $\mathrm{step} > 0$ on $\mathrm{Tuple}$, $\delta > 0$, $\delta^{-1} \le e^{F}$, $\delta L_\iota \le |\{c_\iota + \mathrm{step}_\iota k : k < H_\iota\}|$ for $\iota \in \mathrm{Tuple}$, and $s + 1 \le m + 1$. A full tuple $y_0$ with positive `wholeLaw` weight. Reals $T_j$ with `partitionedIdealRadius (Fin (s+1)) m` $+ 1 \le T_j$ and (number of exponent vectors of degree $\le j+1$ in the sampler variables)$\cdot 2^{s+1}(s+2)^{j+1} \le T_j$. Reals $C_j \ge 0$ with $\lVert \chi_j^{-1}(v) \rVert \le C_j \lVert v \rVert$, where $\chi_j$ = `normalizedOrthogonalChart V_j basis_j` (OpenAI), and $C_j(|I_j| + 1)T_j R_j \le 1/4$. $\rho(\mathrm{grid})^{-1} \le e^{P_\rho}$, $0 \le \eta \le \exp(-(\mathrm{target} + 1 + D\,m 2^{m+1} P_k + 4))$. A real $\mathrm{siteRadius} \ge 1$ with $(|\mathrm{rowSets}_j| + 1)\cdot 2^{s+1}\cdot C_j(|I_j|+1)\,2\,\mathrm{siteRadius}\,R_j \le 1/4$ and $|\mathrm{rowSets}_j|\,T_j \le \mathrm{siteRadius}$ for all $j$. Constants $C^{\mathrm{fwd}}_j \ge 0$ with $\lVert \chi_j(v) \rVert \le C^{\mathrm{fwd}}_j \lVert v \rVert$, and $K \ge 0$ with $R_j^{-1} \le K$.
--
--   **Ambient bounds.** Reals $P_{\mathrm{box}}, V_{\log}, N_{\log}, M_{\log} \ge 0$ and $\mathrm{baseAmbient} \ge 0$ with: $2\cdot$`allocatedRowSlicedSiteRadius rowSets` $\le e^{P_{\mathrm{box}}}$; `allocatedFullGridNaturalVolume B U basis S rowSets` $\le e^{V_{\log}}$; $|1/$`allocatedProductIdealNormalizer B U basis S rowSets`$| \le e^{N_{\log}}$; `layerKernelIndexBound m M_k`$^{(\text{number of axes})}\cdot$`coefficientDeckPeriodCap selectedRows Q period` $\le e^{M_{\log}}$; $V_{\log}, N_{\log}, M_{\log} \le \mathrm{baseAmbient}$; $2^{s+1} \le \mathrm{baseAmbient}$; (number of axes) $\le \mathrm{baseAmbient}$; $\mathrm{period}^{\sum_j n_j + \sum_j |Q_j|} \le e^{\mathrm{baseAmbient}}$ (the number of label pairs); $K \le e^{\mathrm{baseAmbient}}$; $\sum_j C^{\mathrm{fwd}}_j |J_j| \le e^{\mathrm{baseAmbient}}$; `normalizedSiteCutoffBound` $\le e^{\mathrm{baseAmbient}}$; $\mathrm{period} \le e^{\mathrm{baseAmbient}}$; $\sum_j |\mathrm{rowSets}_j| \le e^{\mathrm{baseAmbient}}$; $\sum_{a} |\mathrm{rowSets}_{j(a)}| \le \mathrm{baseAmbient}$ (over all axes $a = (j(a), \cdot)$); $\texttt{S.value}^{\texttt{layerTailDegree}\ m + 1} \le e^{\mathrm{baseAmbient}}$ (all OpenAI quantities).
--
--   **Grid hypotheses.** $Q_{\mathrm{grid}} \ge 0$ with $8(|\texttt{layerIntegerPrincipalSlots}| + 1) \le Q_{\mathrm{grid}}$ at the integer axis of every grid axis; $\delta_g > 0$ with $\delta_g\,\mathrm{side}_\iota \le H_0(\iota)$ for all principal $\iota$; $T_g \in \mathbb{N}$ with $(s+2)\,\mathrm{modulus}/\delta_g \le T_g$; $\mathrm{step}_0 > 0$; $A_g \ge 0$ with `Real.smoothTransition` $A_g$-Lipschitz; $P_g \ge 1$ with `scalarCubePrimitiveEnvelope Empty A_g 16 (128 Λ) 1` $\le P_g$ ($\Lambda$ = `probabilityProfileLipschitz`), `scalarCubePrimitiveEnvelope (Fin (s+1)) A_g 1 0 modulus` $\le P_g$ and $\mathrm{step}_0(\iota)\,\mathrm{modulus} \le P_g$; for all $j$ and $i < n_j$, `positiveModerateSpectrumBlockCount j |rowSets_j| ((layerTailDegree m + 1)|rowSets_j|)` and `uniformSpectrumBlockCount j |rowSets_j| ((j+1)|rowSets_j|)` are at most $|B_{(j,i)}|$. Reals $D_g, v_g, w_g, t_g, p_g \ge 0$ with $s+1 \le D_g$, $j+1 \le D_g$, $|\mathrm{rowSets}_j| \le D_g$, $\texttt{layerTailDegree}\ m + 1 \le D_g$, $|B_{(j,i)}| \le D_g$, $R_j \le e^{v_g}$, $R_j^{-1} \le e^{v_g}$, $\delta_g^{-1} \le e^{w_g}$, $T_g \le e^{t_g}$, (number of exponent vectors of degree $\le j+1$) $\le e^{v_g}$, $P_g \le e^{p_g}$, (number of grid axes), (number of axes), $\sum_a |\mathrm{rowSets}_{j(a)}|$, $\sum_j |J_j|$ and $\Lambda$ all $\le D_g$. A real $B_{\mathrm{an}} \ge 0$ with $D_g \le B_{\mathrm{an}}$, `normalizedSiteCutoffBound` $\le e^{B_{\mathrm{an}}}$, $K\sum_j C^{\mathrm{fwd}}_j|J_j| \le e^{B_{\mathrm{an}}}$, $Q_{\mathrm{grid}} \le e^{B_{\mathrm{an}}}$. A real $P_{\mathrm{num}} \ge 0$ with $|I_j|, n_j$, (number of exponent vectors of degree $\le j+1$) $\le P_{\mathrm{num}}$, $R_j^{-1} \le e^{P_{\mathrm{num}}}$ and `mixedDensityCovolumeRatio V_j basis_j` $\le e^{P_{\mathrm{num}}}$. Finally fix reals $\mathrm{gain}, P_{\mathrm{proj}}, \mathrm{coarseTarget}, E_{\mathrm{coarse}}, p_{\mathrm{Gain}}$.
--
--   **Conclusion part 1 (further universally quantified hypotheses).** Let $\mathrm{ambientQ}$ = `idealSiteLogBudget (Σ_a |rowSets_{j(a)}|) (s+1) (P_box + P_ρ + V_log + N_log + M_log + target)` and $\mathrm{ambientBudget}$ = `affineAmbientPrimitiveBudget baseAmbient ambientQ`. For all reals $\tau, P_{\mathrm{phys}}$, with $W$ = `allocatedPhysicalRootBudget B U basis S (fun _ => 0)`, for every $\xi_n > 0$ with $\xi_n \le$ `normalizedTupleNarrowWidth (Fin n_X) (principal indices) selection M_k P_phys coarseTarget`, every finite set `cells` of column residue patterns (OpenAI's `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin n_X) stride`), all vector polynomials $\mathrm{poly}_j$ in $n_X$ variables of total degree $\le j+1$ with coefficients in $U_j$, and every $\mathrm{signal} : \mathbb{Z}^{n_X} \to \mathbb{C}$ with $|\mathrm{signal}| \le 1$ on the integer box $\prod_i \{0,\dots,N_i - 1\}$ and $\mathrm{signal} = 0$ off it; for all reals $\mathrm{lossTarget}, P_s, R_{\mathrm{rank}}, S_{\mathrm{stride}}, \varepsilon_s, \eta_s$: assume $\mathrm{stride}_i > 0$, $N_i > 0$, $\tau > 0$, $0 \le P_s$, $n_X \le P_s$, $(s+2)n_X \le P_s$, $0 \le S_{\mathrm{stride}} \le e^{P_s}$, $\varepsilon_s > 0$, $1/\tau \le e^{P_s}$, $1/\varepsilon_s \le e^{P_s}$, $\mathrm{stride}_i \le S_{\mathrm{stride}}$; with $A_1$ the constant chosen from `exists_translated_physical_jet_l1_perturbation m (s+1)`: $\exp((P_s + A_1)^{A_1}) \le N_i$ for all $i$, `HasLayerSamplingRank (j+1) N R_rank U_j poly_j` for all $j$, $\exp((P_s + A_1)^{A_1}) \le R_{\mathrm{rank}}$; $\eta_s > 0$; $|$`CoefficientAmbientIndex (Fin (s+1)) J`$| \le P_s$; $\mathrm{ambientBudget} \le P_s$; $\sum_j$(number of exponent vectors on $\mathcal{S}$ of degree $\le j+1$) $\le e^{P_s}$; $\eta_s^{-1} \le e^{P_s}$. With $V'$ = `narrowTrimmedSpatialWidths W τ ξ_n N`: assume $0 \le P_{\mathrm{phys}}$, $M_k \le e^{P_{\mathrm{phys}}}$, $m+1 \le P_{\mathrm{phys}}$, $0 \le \mathrm{coarseTarget}$, $s+2 \le P_{\mathrm{phys}}$, $|G| \le P_{\mathrm{phys}}$, $n_X \le P_{\mathrm{phys}}$, $\mathrm{lossTarget} +$ `coefficientErrorSpatialLog P_phys` $+ 8 \le \mathrm{target}$, $\eta_s \le e^{-\mathrm{target}}$, $\varepsilon_s \le e^{-\mathrm{target}}$. Let $A_{\mathrm{mass}}$, $A_{\mathrm{an}}$ be the constants chosen from `exists_allocatedAffineModelMass_budget m (s+1)` and `exists_allocatedAffineAnalytic_budget m (s+1)`, let
--   $$F_{\mathrm{model}} = m\,2^{s+1}(P_{\mathrm{num}} + 8)(1 + 4P_{\mathrm{num}}) + (\text{number of axes})\cdot m 2^{m+1} P_k + \sum_j |Q_j|\,|\mathrm{rowSets}_j|\,(m+1)P_k,$$
--   and $p$ = `slicedGridGeometryLog D_g v_g w_g t_g` $+ p_g$. For every $P_{\mathrm{native}} \ge 0$ such that $D_g, p, v_g, F_{\mathrm{model}}, P_\rho, P_k, \mathrm{target}, B_{\mathrm{an}}, P_{\mathrm{phys}}, E_{\mathrm{coarse}}, p_{\mathrm{Gain}}$ all lie in $[0, P_{\mathrm{native}}]$, assume further: $\mathrm{stride}_i \le e^{P_{\mathrm{phys}}}$, $1/\tau \le e^{P_{\mathrm{phys}}}$, $e^{-p_{\mathrm{Gain}}}/2 \le \mathrm{gain}$, and $p_{\mathrm{Gain}} + 32$ is at most each of $P_{\mathrm{proj}}$, $\mathrm{coarseTarget}$, $E_{\mathrm{coarse}}$, $\mathrm{lossTarget}$. For all $C^{\mathrm{proj}}_j, V^{\mathrm{proj}}_j \ge 0$: with $A_{\mathrm{cover}}$ and $A_{\mathrm{proj}}$ the two constants chosen from `exists_allocated_canonical_constructed_projection m (s+1)`, $\mathrm{coverLog} = (P_{\mathrm{proj}} + s + 3 + A_{\mathrm{cover}})^{A_{\mathrm{cover}}}$, $A_{\mathrm{sample}}$ chosen from `exists_allocatedCanonicalProjection_composed_budget m (s+1) A_cover`, $P_{\mathrm{mass}} = (P_{\mathrm{proj}} + A_{\mathrm{sample}})^{A_{\mathrm{sample}}}$: assume $\mathrm{coverLog} \le \mathrm{baseAmbient}$, $\mathrm{coverLog} \le P_s$, $P_{\mathrm{mass}} \le P_s$; $\lVert \chi_j(z) \rVert \le C^{\mathrm{proj}}_j \lVert z \rVert$; $0 \le$ `mixedDensityCovolumeRatio V_j basis_j` $\le V^{\mathrm{proj}}_j$; $\sigma_j \le 1$; $C_j(|I_j| + 1)R_j \le 1/4$; $n_X \le P_{\mathrm{mass}}$, $(s+2)n_X \le P_{\mathrm{mass}}$, $\mathrm{stride}_i \le e^{P_{\mathrm{mass}}}$, $1/\tau \le e^{P_{\mathrm{mass}}}$; with $A_{\mathrm{win}}$ chosen from `exists_translated_physical_jet_density_window_mass m (s+1)`: $\exp((P_{\mathrm{mass}} + A_{\mathrm{win}})^{A_{\mathrm{win}}}) \le N_i$ and $\le R_{\mathrm{rank}}$; $|$`CoefficientAmbientIndex (Fin (s+1)) J`$| \le P_{\mathrm{mass}}$; $\sum_j$(number of exponent vectors on $\mathcal{S}$ of degree $\le j+1$) $\le e^{P_{\mathrm{mass}}}$; (number of layer sampler variables) $\le e^{P_{\mathrm{phys}}}$; $1 \le P_{\mathrm{proj}}$, $m \le P_{\mathrm{proj}}$, $|G| \le P_{\mathrm{proj}}$, $\texttt{S.value} \le e^{P_{\mathrm{proj}}}$, $(m+1)P_k \le P_{\mathrm{proj}}$, (number of layer sampler variables) $\le P_{\mathrm{proj}}$, $W \le e^{P_{\mathrm{proj}}}$, $R_j^{-1}, \sigma_j^{-1} \le e^{P_{\mathrm{proj}}}$, (number of exponent vectors of degree $\le j+1$) $\le P_{\mathrm{proj}}$, $|I_j|, n_j, |J_j| \le P_{\mathrm{proj}}$, $\Lambda \le e^{P_{\mathrm{proj}}}$, $C^{\mathrm{proj}}_j, V^{\mathrm{proj}}_j \le e^{P_{\mathrm{proj}}}$, $n_X \le P_{\mathrm{proj}}$, (number of layer sampler variables $+1$)$\cdot n_X \le P_{\mathrm{proj}}$, $\mathrm{stride}_i \le e^{P_{\mathrm{proj}}}$, $\tau^{-1} \le e^{P_{\mathrm{proj}}}$, $\xi_n^{-1} \le e^{P_{\mathrm{proj}}}$; $\exp((P_{\mathrm{proj}} + A_{\mathrm{proj}})^{A_{\mathrm{proj}}}) \le N_i$ and $\le R_{\mathrm{rank}}$. For every real $P_{\mathrm{side}}$ at least $P_{\mathrm{proj}}$, $P_{\mathrm{mass}}$, $P_{\mathrm{phys}}$ and $\mathrm{coarseTarget}$, with $A_{\mathrm{cut}}$ chosen from `exists_allocatedCanonicalSpatial_cutoff m`: assume $\exp((P_{\mathrm{side}} + A_{\mathrm{cut}})^{A_{\mathrm{cut}}} + P_{\mathrm{proj}}) \le N_i$ for all $i$; `cells` is nonempty; let `bases` be a nonempty finite set of integer vectors in $\mathbb{Z}^{n_X}$; assume $0 < \sum_z$ `selectedResidueSmoothWeight stride cells V' z`; and assume
--   $$\mathrm{gain} \le \operatorname{Re}\,\mathbb{E}_{y \sim \mathrm{wholeLaw}}\, \texttt{allocatedSlicedTupleValue}(\ldots, \mathrm{poly}, N, \tau, \xi_n, \mathrm{stride}, \mathrm{cells}, \mathrm{bases}, x, y, \mathrm{signal})$$
--   (an OpenAI complex function).
--
--   **Conclusion part 2.** Let $C^{*}$ be the constant chosen from `exists_canonicalSlicedNative_input_budget m (s+1) A_mass A_an`, $B^{*} = (P_{\mathrm{native}} + C^{*})^{C^{*}}$, $A_{\mathrm{norm}}$ chosen from `exists_allocatedRecenteredFactor_normalization m (s+1)`, $A_{\mathrm{nat}}$ chosen from `exists_native_partner_of_physical_cube_mixture_all_degrees s`, $A^{*}$ chosen from `exists_normalizedNative_uniform_budget m A_norm A_nat`, and $\mathrm{budget} = (B^{*} + A^{*})^{A^{*}}$. Then there exist a twist $\Theta$ (an OpenAI `NormalizedPolynomialTwist (Fin n_X) (Σ j, J j)` with modulus cap, cover cap and Lipschitz constant all equal to $e^{\mathrm{budget}}$) and a function $F_{\mathrm{native}}$ on the integer box such that there is a `NativeSampleModel (fun _ => 1) s budget (fun u => u) F_native` (an OpenAI structure) and
--   $$e^{-\mathrm{budget}} \le \Bigl|\, \mathbb{E}_{u}\, \mathrm{signal}(u)\cdot \overline{\overline{\Theta.\mathrm{eval}(N, \mathrm{poly}, u)}\, F_{\mathrm{native}}(u)}\Bigr| = \Bigl|\, \mathbb{E}_{u}\, \mathrm{signal}(u)\, \Theta.\mathrm{eval}(N, \mathrm{poly}, u)\, \overline{F_{\mathrm{native}}(u)}\Bigr|,$$
--   where $u$ is uniform on the integer box (this is OpenAI's `correlation` of $u \mapsto \mathrm{signal}(u)$ with $u \mapsto \overline{\Theta.\mathrm{eval}(N, \mathrm{poly}, u)}\, F_{\mathrm{native}}(u)$, the mean of the first function times the conjugate of the second), and `Θ.eval N poly u` is the mask of $\Theta$ at $u$ modulo its modulus times its smooth part at $(u_i/N_i)_i$ and OpenAI's physical grid factor input of the polynomials at $u$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_spatial_native_source_sharedWidth_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_spatial_native_source_sharedWidth` (in `lean/OAI/Combinatorics/Progressions/Geometry/SharedWidthAllocatedCanonicalSpatialNativeSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B277` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/SharedWidthAllocatedCanonicalSpatialNativeSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_spatial_native_source_sharedWidth)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uQ
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal
attribute [local irreducible] residueRefinedPeriod

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin (s + 1) ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable (period : ℕ) [NeZero period] (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (hperiodCanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m))
variable (modulus : ℕ)
variable (hmodulusRefined : modulus = residueRefinedPeriod period stride)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin (s + 1))) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell

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

include hb o bW hperiodCanonical hmodulusRefined μ ν μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in

theorem exists_allocatedCanonicalSlice_spatial_native_source_sharedWidth_s2
    {D target Pk Prho F Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hPk : 0 ≤ Pk)
    (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho)
    (htarget : 0 ≤ target)
    (hF : 0 ≤ F)
    (hQstride : 0 ≤ Qstride)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    {δ η : ℝ}
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (t : ℝ)
    (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid)
    (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ)
    (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hq : Fintype.card (Fin (s + 1)) ≤ m + 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U basis S))
    (hy₀ : 0 < (wholeLaw).weight y₀)
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
    (hmask : (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap selectedRows Q period ≤ Real.exp Mlog)
    (hbaseAmbient : 0 ≤ baseAmbient)
    (hvbase : Vlog ≤ baseAmbient)
    (hnbase : Nlog ≤ baseAmbient)
    (hmbase : Mlog ≤ baseAmbient)
    (hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤ Real.exp baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hpbase : (period : ℝ) ≤ Real.exp baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0)
    (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    {δg : ℝ}
    (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U basis S tg ≤ (H₀ tg : ℝ))
    (Tg : ℕ)
    (hQTg : (((Fintype.card (Fin (s + 1)) + 1) * modulus : ℕ) : ℝ) / δg ≤ Tg)
    (hstepAll : ∀ tg, 0 < step₀ tg)
    (Ag : ℝ≥0)
    (hAg : LipschitzWith Ag Real.smoothTransition)
    (Pg : ℝ)
    (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin (s + 1)) Ag 1 0 modulus ≤ Pg)
    (hstrideGrid : ∀ tg, ((step₀ tg * modulus : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg)
    (hvg : 0 ≤ vg)
    (hwg : 0 ≤ wg)
    (htg : 0 ≤ tg)
    (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg)
    (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg)
    (hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg)
    (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg)
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
    {gain Pproj coarseTarget Ecoarse pGain : ℝ}
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {τ Pphysical : ℝ},
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn),
    ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection Mk Pphysical coarseTarget →
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
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,uJ,0} m (s + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (hPhysicalNonneg : 0 ≤ Pphysical) → (hMkPhysicalBound : (Mk : ℝ) ≤ Real.exp Pphysical) →
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
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ gain →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    ∀ (Cproj Vproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,uG,uI,uB,uJ} m (s + 1))
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
    let AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,uJ,0,max uG uI uB} m (s + 1))
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
      (exists_allocated_canonical_constructed_projection.{0,uG,uI,uB,uJ} m (s + 1)))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
    ∀ {Pside : ℝ}, Pproj ≤ Pside → Pmass ≤ Pside →
    Pphysical ≤ Pside → coarseTarget ≤ Pside →
    (∀ i, Real.exp ((Pside + Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{uG,uI,uB,0} m)) ^
      Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{uG,uI,uB,0} m) + Pproj) ≤ (N i : ℝ)) →
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), bases.Nonempty →
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    gain ≤ ((wholeLaw).complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S
      (Fin nX) poly hmem N (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW
      hτSpatial hξn stride cells hmass bases x y signal)).re →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
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
end
