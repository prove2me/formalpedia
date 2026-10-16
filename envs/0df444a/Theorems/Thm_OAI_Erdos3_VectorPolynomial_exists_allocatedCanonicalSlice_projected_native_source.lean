-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_projected_native_source
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projected_native_source
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:46:15.077658+00:00
-- url     : https://prove2.me/theorems/bfa711f1-6a02-48e2-8ef7-c5109c039d58
-- title:
--   A large sliced tuple value at the canonical period gives a twisted native correlation
-- statement:
--   Fix the section data (with universe levels $u_G, u_I, u_B, u_J, u_Q$): a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$, $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L_S = $ `S.value`; natural numbers $s$ and $n_X$, with row sets $\mathrm{rowSets}_j = $ `boundedBooleanJetRows (Fin (s+1)) (j+1)` (subsets of size at most $j+1$), row types $\mathrm{selectedRows}_j$ and inclusions $\mathrm{rows}_j$; grid is the predicate `allocatedGridAxis U basis L_S` on axes, Tuple is the tuple index over the non-grid axes, and $L$ the side lengths `allocatedPrincipalSides B U basis S` restricted to Tuple; a point $x : G \to $ `IntegerScalarCubeBox (Fin (s+1)) L_S`; a natural number $M_k > 0$, an embedding $\mathrm{selection} : \mathrm{Fin}(s+1) \hookrightarrow G$ and $hgood$: `GoodScalarKernelTuple selection (1/Mk) Mk x`; a natural number $\mathrm{period} \neq 0$ and $\mathrm{stride}, N : \mathrm{Fin}\,n_X \to \mathbb N$ with every $N_i \neq 0$; $hperiodCanonical$: $\mathrm{period} = $ `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hgood m)`; a natural number $\mathrm{modulus}$ with $\mathrm{modulus} = $ `residueRefinedPeriod period stride` $= \mathrm{period}\prod_i \mathrm{stride}_i$; a real $P \ge 0$ with $M_k \le e^{P}$, $R_j \le e^{P}$, $R_j^{-1} \le e^{P}$, $\sigma_j^{-1} \le e^{P}$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^{P}$; finite types $Q_j$; $hb$: the $\mathbb Z$-span of $\mathrm{basis}_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $Q_j$; natural-valued $H_0, \mathrm{step}_0$ and integer-valued $c_0$ on `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H_0 > 0$ and each progression $\{c_0(t) + \mathrm{step}_0(t)k : 0 \le k < H_0(t)\}$ contained in $[0, \texttt{allocatedPrincipalSides B U basis S t})$; $H, \mathrm{step}, c$ their restrictions to Tuple; a label $r_0 :$ tuple index $\to \mathrm{Option}(\mathrm{Fin}(s+1)) \to \mathbb Z/\mathrm{modulus}$ with $hcell$: positive mass of the tuples with residue label $r_0$ under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀`; wholeLaw $=$ `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ _ hH₀ hsubset₀ modulus r₀ hcell`; the assumption that each $\mathbb Z^{J_j} \cap V_j$ is a full lattice in $V_j$; additively left-invariant probability measures $\nu_j$ on $V_j/(\mathbb Z^{J_j} \cap V_j)$; compact Borel structures on `CoefficientTorus (LayerSamplerVariables G I n B) U` and `CoefficientTorus (Fin (s+1)) U` with additively left-invariant probability measures $\mu$ and $\mu_{\mathrm{rows}}$; and a Borel structure on `SiteTorus (Finset (Fin (s+1))) U`. The measures $\nu, \mu, \mu_{\mathrm{rows}}$, the bases $o, bW$, and the hypotheses $hb$, $hperiodCanonical$, the modulus identity, $R > 0$, $\sigma > 0$, $M_k > 0$, $hgood$ and the bounds involving $P$ are all hypotheses of the theorem.
--
--   Explicit hypotheses (first group): reals $D, \mathrm{target}, P_k, P_\rho, F, Q_{\mathrm{stride}}$ with `AllocatedComparisonDimensions B (Fin (s+1)) selectedRows D` (OpenAI's predicate that $D \ge 0$ bounds $m$, $|G|$, $s+1$ and a list of cardinalities), $P_k \ge 0$, $M_k \le e^{P_k}$, $P_\rho, \mathrm{target}, F, Q_{\mathrm{stride}} \ge 0$, $\mathrm{stride}_i > 0$, $\mathrm{stride}_i \le e^{Q_{\mathrm{stride}}}$, and $\exp(\texttt{allocatedAffineLengthLog m D P Prho Pk target F}((m+1)P_k + n_X Q_{\mathrm{stride}})) \le L_S$; reals $\delta, \eta$, $\rho$ assigning to each predicate on axes an element of $\mathbb R_{\ge 0}$, and $t \le 1$ with `AllocatedAffineCoveredComparison B rows δ η ρ t htone` (OpenAI's comparison predicate quantifying over all layer data of universe $u_J$, $u_Q$), $0 < \rho(\mathrm{grid}) \le 1$, $\sigma_j \le t$, $\mathrm{step}_j > 0$ on Tuple, $\delta > 0$, $\delta^{-1} \le e^{F}$, $\delta L_j \le |\{c_j + \mathrm{step}_j k : 0 \le k < H_j\}|$ on Tuple, $s+1 \le m+1$; a tuple $y_0$ with $\mathrm{wholeLaw}(y_0) > 0$; $T : \mathrm{Fin}\,m \to \mathbb R$ with `partitionedIdealRadius (Fin (s+1)) m` $+1 \le T_j$ and $|\texttt{BoundedCoefficientExponent}\dots(j+1)|\cdot 2^{s+1}(s+2)^{j+1} \le T_j$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ \mathrm{basis}_j)^{-1}v\| \le C_j\|v\|$ and $C_j(|I_j|+1)T_jR_j \le 1/4$; $\rho(\mathrm{grid})^{-1} \le e^{P_\rho}$; $0 \le \eta \le \exp(-(\mathrm{target} + 1 + D\,m2^{m+1}P_k + 4))$; $\mathrm{siteRadius} \in \mathbb R_{\ge 0}$ with $1 \le \mathrm{siteRadius}$ and $(|\mathrm{rowSets}_j|+1)\,|\mathcal P(\mathrm{Fin}(s+1))|\,C_j(|I_j|+1)\,2\,\mathrm{siteRadius}\,R_j \le 1/4$; $C_{\mathrm{forward}}$ with $\|\texttt{normalizedOrthogonalChart}\ V_j\ \mathrm{basis}_j\ v\| \le C_{\mathrm{forward}}(j)\|v\|$; $K \ge R_j^{-1}$; $|\mathrm{rowSets}_j|\,T_j \le \mathrm{siteRadius}$; reals $P_{\mathrm{box}}, V_{\log}, N_{\log}, M_{\log}, \mathrm{baseAmbient} \ge 0$ with $2\,$`allocatedRowSlicedSiteRadius rowSets` $\le e^{P_{\mathrm{box}}}$, `allocatedFullGridNaturalVolume B U basis S rowSets` $\le e^{V_{\log}}$, $\|(\texttt{allocatedProductIdealNormalizer B U basis S rowSets})^{-1}\| \le e^{N_{\log}}$, $(\texttt{layerKernelIndexBound}\ m\ M_k)^{|\texttt{LayerSamplerAxis I n}|}\cdot$`coefficientDeckPeriodCap selectedRows Q period` $\le e^{M_{\log}}$, $V_{\log}, N_{\log}, M_{\log}, |\mathcal P(\mathrm{Fin}(s+1))|, |\texttt{LayerSamplerAxis I n}|, |\Sigma_a\,\mathrm{selectedRows}_{a.1}| \le \mathrm{baseAmbient}$, and $|(\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}) \times (\prod_j Q_j \to \mathbb Z/\mathrm{period})|$, $K$, $\sum_j C_{\mathrm{forward}}(j)|J_j|$, `normalizedSiteCutoffBound`, $\mathrm{period}$, $\sum_j|\mathrm{rowSets}_j|$, $L_S^{\texttt{layerTailDegree}\ m+1}$ each $\le e^{\mathrm{baseAmbient}}$; $Q_{\mathrm{grid}} \ge 8(|\texttt{layerIntegerPrincipalSlots B (allocatedGridIntegerAxis B U basis S a)}|+1)$ for grid axes $a$; $\delta_g > 0$ with $\delta_g\cdot\texttt{allocatedPrincipalSides}(t) \le H_0(t)$; a natural number $T_g \ge (s+2)\,\mathrm{modulus}/\delta_g$; $\mathrm{step}_0 > 0$; $A_g$ a Lipschitz constant of `Real.smoothTransition`; $P_g \ge 1$ with `scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1` $\le P_g$, `scalarCubePrimitiveEnvelope (Fin (s+1)) Ag 1 0 modulus` $\le P_g$, $\mathrm{step}_0(t)\,\mathrm{modulus} \le P_g$; the block-count bounds `positiveModerateSpectrumBlockCount j |rowSets j| ((layerTailDegree m + 1)|rowSets j|)` $\le |B_{(j,\mathrm{inr}\,i)}|$ and `uniformSpectrumBlockCount j |rowSets j| ((j+1)|rowSets j|)` $\le |B_{(j,\mathrm{inr}\,i)}|$; reals $D_g, v_g, w_g, t_g, p_g \ge 0$ with $s+1, j+1, |\mathrm{rowSets}_j|, \texttt{layerTailDegree}\ m + 1, |B_{(j,\mathrm{inr}\,i)}|, \#\text{grid axes}, |\texttt{LayerSamplerAxis I n}|, |\Sigma_a\,\mathrm{selectedRows}_{a.1}|, \sum_j|J_j|, \texttt{probabilityProfileLipschitz} \le D_g$, $R_j, R_j^{-1} \le e^{v_g}$, $\delta_g^{-1} \le e^{w_g}$, $T_g \le e^{t_g}$, $|\texttt{BoundedCoefficientExponent}\dots(j+1)| \le e^{v_g}$, $P_g \le e^{p_g}$; $B_{\mathrm{analytic}} \ge 0$ with $D_g \le B_{\mathrm{analytic}}$ and `normalizedSiteCutoffBound`, $K\sum_j C_{\mathrm{forward}}(j)|J_j|$, $Q_{\mathrm{grid}}$ each $\le e^{B_{\mathrm{analytic}}}$; $P_{\mathrm{num}} \ge 0$ with $|I_j|, n_j, |\texttt{BoundedCoefficientExponent}\dots(j+1)| \le P_{\mathrm{num}}$, $R_j^{-1} \le e^{P_{\mathrm{num}}}$, `mixedDensityCovolumeRatio V_j basis_j` $\le e^{P_{\mathrm{num}}}$; and reals $\mathrm{gain}, P_{\mathrm{proj}}, \mathrm{coarseTarget}, E_{\mathrm{coarse}}, p_{\mathrm{Gain}}$ (no hypotheses yet).
--
--   Conclusion. Put $\mathrm{ambientQ} = $ `idealSiteLogBudget (card (Σ a, selectedRows a.1)) (s+1) (Pbox + Prho + Vlog + Nlog + Mlog + target)` and $\mathrm{ambientBudget} = $ `affineAmbientPrimitiveBudget baseAmbient ambientQ`. For all reals $W \ge 0$, $\tau$, $\xi_n$, every finite set $\mathrm{cells}$ of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride`, all vector polynomials $\mathrm{poly}_j \in$ `VectorPolynomial (Fin nX) ℝ (J j → ℝ)` of total degree at most $j+1$ with coefficients in $U_j$, and every signal $\phi : \mathbb Z^{n_X} \to \mathbb C$ with $\|\phi\| \le 1$ on `integerBox N` and $\phi = 0$ outside it, and all reals $\mathrm{lossTarget}, P_{\mathrm{physical}}, D_{\mathrm{physical}}, P_{\mathrm{sample}}, R_{\mathrm{rank}}, S_{\mathrm{stride}}, \varepsilon_{\mathrm{sample}}, \eta_{\mathrm{sample}}, \rho_{\mathrm{physical}}, P_{\mathrm{native}}, C_0, \delta_{\mathrm{spatial}}, \mathrm{fineMesh}$ and all $C_{\mathrm{proj}}, V_{\mathrm{proj}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$, assume all of the following:
--
--   - $\mathrm{stride}_i > 0$, $N_i > 0$, $\tau > 0$, `allocatedPhysicalRootBudget B U basis S 0` $\le W$;
--   - $P_{\mathrm{sample}} \ge 0$, $n_X \le P_{\mathrm{sample}}$, $|\mathrm{Option}(\mathrm{Fin}(s+1)) \times \mathrm{Fin}\,n_X| \le P_{\mathrm{sample}}$, $0 \le S_{\mathrm{stride}} \le e^{P_{\mathrm{sample}}}$, $\varepsilon_{\mathrm{sample}} > 0$, $1/\tau, 1/\varepsilon_{\mathrm{sample}} \le e^{P_{\mathrm{sample}}}$, $\mathrm{stride}_i \le S_{\mathrm{stride}}$; with $A$ the natural number chosen by `exists_translated_physical_jet_l1_perturbation m (s+1)`, $\exp((P_{\mathrm{sample}} + A)^A) \le N_i$, `HasLayerSamplingRank (j+1) N R_rank (U j) (poly j)` for all $j$, $\exp((P_{\mathrm{sample}} + A)^A) \le R_{\mathrm{rank}}$; $\eta_{\mathrm{sample}} > 0$, $|\texttt{CoefficientAmbientIndex (Fin (s+1)) J}| \le P_{\mathrm{sample}}$, $\mathrm{ambientBudget} \le P_{\mathrm{sample}}$, $\sum_j|\texttt{BoundedCoefficientExponent (Fin (s+1)) (j+1)}| \le e^{P_{\mathrm{sample}}}$, $\eta_{\mathrm{sample}}^{-1} \le e^{P_{\mathrm{sample}}}$;
--   - with $\mathcal V = $ `narrowTrimmedSpatialWidths W τ ξn N`: $\mathcal V(z) > 0$ for all $z$, and $\sum_z$ `selectedResidueSmoothWeight stride cells 𝒱 z` $> 0$ ($hZ$);
--   - $\xi_n \le 1$, $8(1+W)\,\mathrm{stride}_t\,\rho_{\mathrm{physical}} \le \xi_n\tau N_t$, $8\,$`probabilityProfileLipschitz` $\le \rho_{\mathrm{physical}}$, $2\,|\mathrm{Option}(\texttt{LayerSamplerVariables G I n B})|\cdot 2\,$`allocatedPhysicalEntryBudget B U basis S 0` $\le \rho_{\mathrm{physical}}$;
--   - $P_{\mathrm{physical}} \ge 0$, $M_k \le e^{P_{\mathrm{physical}}}$, $\mathrm{period} \le e^{P_{\mathrm{physical}}^2}$, $s+2, |G|, n_X \le P_{\mathrm{physical}}$, $D_{\mathrm{physical}} \le e^{P_{\mathrm{physical}}}$, $W \le D_{\mathrm{physical}} L_S$, $\mathrm{lossTarget} + $ `coefficientErrorSpatialLog Pphysical` $+ 8 \le \mathrm{target}$, $\eta_{\mathrm{sample}}, \varepsilon_{\mathrm{sample}} \le e^{-\mathrm{target}}$;
--   - with $A_{\mathrm{mass}}, A_{\mathrm{analytic}}$ chosen by `exists_allocatedAffineModelMass_budget m (s+1)` and `exists_allocatedAffineAnalytic_budget m (s+1)`, $F_{\mathrm{model}} = m2^{s+1}(P_{\mathrm{num}}+8)(1+4P_{\mathrm{num}}) + |\texttt{LayerSamplerAxis I n}|\,m2^{m+1}P_k + \sum_j |Q_j|\,|\mathrm{selectedRows}_j|\,(m+1)P_k$ and $p = $ `slicedGridGeometryLog Dg vg wg tg` $+ p_g$: $P_{\mathrm{native}} \ge 0$ and $D_g, p, v_g, F_{\mathrm{model}}, P_\rho, P_k, \mathrm{target}, B_{\mathrm{analytic}}, P_{\mathrm{physical}}, E_{\mathrm{coarse}}, p_{\mathrm{Gain}} \in [0, P_{\mathrm{native}}]$;
--   - $\xi_n > 0$, $\mathrm{stride}_i \le e^{P_{\mathrm{physical}}}$, $1/\tau \le e^{P_{\mathrm{physical}}}$, $e^{-p_{\mathrm{Gain}}}/2 \le \mathrm{gain}$, and $p_{\mathrm{Gain}} + 32 \le P_{\mathrm{proj}}, \mathrm{coarseTarget}, E_{\mathrm{coarse}}, \mathrm{lossTarget}$;
--   - with $A_{\mathrm{cover}}$ (and later $A_{\mathrm{proj}}$) the two natural numbers chosen by `exists_allocated_canonical_constructed_projection m (s+1)`, $\mathrm{coverLog} = (P_{\mathrm{proj}} + s + 3 + A_{\mathrm{cover}})^{A_{\mathrm{cover}}}$, $A_{\mathrm{sample}}$ chosen by `exists_allocatedCanonicalProjection_composed_budget m (s+1) A_cover` and $P_{\mathrm{mass}} = (P_{\mathrm{proj}} + A_{\mathrm{sample}})^{A_{\mathrm{sample}}}$: $\mathrm{coverLog} \le \mathrm{baseAmbient}$, $\mathrm{coverLog} \le P_{\mathrm{sample}}$, $P_{\mathrm{mass}} \le P_{\mathrm{sample}}$; $\|\texttt{normalizedOrthogonalChart}\ V_j\ \mathrm{basis}_j\ z\| \le C_{\mathrm{proj}}(j)\|z\|$; $0 \le$ `mixedDensityCovolumeRatio V_j basis_j` $\le V_{\mathrm{proj}}(j)$; $\sigma_j \le 1$; $C_j(|I_j|+1)R_j \le 1/4$; $n_X, |\mathrm{Option}(\mathrm{Fin}(s+1)) \times \mathrm{Fin}\,n_X| \le P_{\mathrm{mass}}$; $\mathrm{stride}_i, 1/\tau \le e^{P_{\mathrm{mass}}}$; with $A_w$ chosen by `exists_translated_physical_jet_density_window_mass m (s+1)`, $\exp((P_{\mathrm{mass}} + A_w)^{A_w}) \le N_i$ and $\le R_{\mathrm{rank}}$; $|\texttt{CoefficientAmbientIndex (Fin (s+1)) J}| \le P_{\mathrm{mass}}$; $\sum_j|\texttt{BoundedCoefficientExponent (Fin (s+1)) (j+1)}| \le e^{P_{\mathrm{mass}}}$;
--   - $\rho_{\mathrm{physical}} > 0$, $1 \le C_0$, $L_S \le C_0$, $W \le C_0$, `anisotropicSpatialMeshThreshold selection (tuple index) C₀` $\le \rho_{\mathrm{physical}}$, $\delta_{\mathrm{spatial}} \ge 0$, $|\text{tuple index}|\cdot 2\,$`allocatedPhysicalEntryBudget B U basis S 0` $\le \delta_{\mathrm{spatial}}\rho_{\mathrm{physical}}$, $\mathrm{fineMesh} > 0$; $e^{P_{\mathrm{mass}}}\cdot 24\,\texttt{probabilityProfileLipschitz}\cdot|\mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times \mathrm{Fin}\,n_X|/\rho_{\mathrm{physical}} \le$ `normalizedSpatialShare coarseTarget`$/2$; `allocatedTupleSpatialError nX selection (tuple index) Mk period C₀ ρphysical ξn W δspatial fineMesh` $\cdot$ `coarseReferenceMassConstant (s+1) (Fin nX) W L_S` $\le$ `normalizedSpatialShare coarseTarget`$/2$; $|\texttt{LayerSamplerVariables G I n B}| \le e^{P_{\mathrm{physical}}}$; $W \le |\texttt{LayerSamplerVariables G I n B}|\,L_S$; $\mathrm{fineMesh} \le$ `allocatedEarlyRecenteredMesh (Fin nX) selection Mk period Pphysical Ecoarse`;
--   - $1 \le P_{\mathrm{proj}}$, $m, |G| \le P_{\mathrm{proj}}$, $L_S \le e^{P_{\mathrm{proj}}}$, $(m+1)P_k \le P_{\mathrm{proj}}$, $|\texttt{LayerSamplerVariables G I n B}| \le P_{\mathrm{proj}}$, $W \le e^{P_{\mathrm{proj}}}$, $R_j^{-1}, \sigma_j^{-1} \le e^{P_{\mathrm{proj}}}$, $|\texttt{BoundedCoefficientExponent}\dots(j+1)|, |I_j|, n_j, |J_j| \le P_{\mathrm{proj}}$, `probabilityProfileLipschitz`, $C_{\mathrm{proj}}(j), V_{\mathrm{proj}}(j) \le e^{P_{\mathrm{proj}}}$, $n_X, |\mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times \mathrm{Fin}\,n_X| \le P_{\mathrm{proj}}$, $\mathrm{stride}_i, \tau^{-1}, \xi_n^{-1} \le e^{P_{\mathrm{proj}}}$, $\exp((P_{\mathrm{proj}} + A_{\mathrm{proj}})^{A_{\mathrm{proj}}}) \le N_i$ and $\le R_{\mathrm{rank}}$;
--   - $\mathrm{cells}$ is nonempty; and for a nonempty finite set $\mathrm{bases} \subseteq \mathbb Z^{n_X}$, $\mathrm{gain} \le \mathrm{Re}\,\mathbb E_{y \sim \mathrm{wholeLaw}}$ `allocatedSlicedTupleValue B U basis hb o hR hσ S (Fin nX) poly hmem N _ hW hτ hξn stride cells hZ bases x y φ`.
--
--   Then, with $C$ chosen by `exists_canonicalSlicedNative_input_budget m (s+1) A_mass A_analytic`, $B_{\mathrm{budget}} = (P_{\mathrm{native}} + C)^C$, $A_{\mathrm{norm}}$ chosen by `exists_allocatedRecenteredFactor_normalization m (s+1)`, $A_{\mathrm{native}}$ chosen by `exists_native_partner_of_physical_cube_mixture_all_degrees s`, $A'$ chosen by `exists_normalizedNative_uniform_budget m A_norm A_native` (all existence theorems of OpenAI) and $\mathrm{budget} = (B_{\mathrm{budget}} + A')^{A'}$, there exist twistData : `NormalizedPolynomialTwist (Fin nX) (Σ j, J j) (exp budget) (exp budget) (exp budget)` (a modulus and a cover, positive and at most $e^{\mathrm{budget}}$, a residue mask of norm $\le 1$ and an $e^{\mathrm{budget}}$-Lipschitz smooth factor of norm $\le 1$) and $F_{\mathrm{native}} : $ `integerBox N` $\to \mathbb C$ such that `NativeSampleModel (fun _ => 1) s budget (fun u => u) Fnative` is nonempty ($F_{\mathrm{native}}$ is the evaluation of a niltest of norm bound $\le 1$ and complexity $\le \mathrm{budget}$ on a rational filtered nilmanifold of degree $s$) and
--   $$e^{-\mathrm{budget}} \le \Bigl\|\mathbb E_{u \in \texttt{integerBox N}}\ \phi(u)\,\overline{\overline{\texttt{twistData.eval N poly}(u)}\,F_{\mathrm{native}}(u)}\Bigr\|.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projected_native_source` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalProjectedNativeSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B178`, `OAIErdos3B199`, `OAIErdos3B1323`, `OAIErdos3B1328` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalProjectedNativeSource.lean#L885

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B178
import Definitions.Def_OAIErdos3B199
import Definitions.Def_OAIErdos3B1323
import Definitions.Def_OAIErdos3B1328

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))



variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uQ uX₀
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin (s + 1) ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable {X₀ : Type uX₀} [Fintype X₀] (stride₀ : X₀ → ℕ)
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
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin (s + 1))) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))

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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uQ
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

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
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin (s + 1) ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable (period : ℕ) [NeZero period] (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (hperiodCanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m))
variable (modulus : ℕ) (hmodulusRefined : modulus = residueRefinedPeriod period stride)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
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
local notation "wholeLaw" => containedSupportedProgressionLaw (α := Fin (s + 1)) B (layerSamplerDegree I n)
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

include ν μ hb o bW hperiodCanonical hmodulusRefined μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in
theorem exists_allocatedCanonicalSlice_projected_native_source
    {D target Pk Prho F Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hQstride : 0 ≤ Qstride)
    (hstride : ∀ i, 0 < stride i) (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hq : Fintype.card (Fin (s + 1)) ≤ m + 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U basis S))
    (hy₀ : 0 < (wholeLaw).weight y₀)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) * ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (siteRadius : ℝ≥0) (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
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
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U basis S tg ≤ (H₀ tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin (s + 1)) + 1) * modulus : ℕ) : ℝ) / δg ≤ Tg)
    (hstepAll : ∀ tg, 0 < step₀ tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin (s + 1)) Ag 1 0 modulus ≤ Pg)
    (hstrideGrid : ∀ tg, ((step₀ tg * modulus : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ} (hBanalytic : 0 ≤ Banalytic) (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {gain Pproj coarseTarget Ecoarse pGain : ℝ}
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {W τ ξn : ℝ} (hW : 0 ≤ W)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (signal : ((Fin nX) → ℤ) → ℂ),
    (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    ∀ {lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → ∀ (hτ : 0 < τ),
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
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
    (∀ z, 0 < V z) → ∀ (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    ∀ {ρphysical : ℝ}, ξn ≤ 1 →
    (∀ t, 8 * (1 + W) * (stride t : ℝ) * ρphysical ≤ (ξn * τ) * (N t : ℝ)) →
    8 * (probabilityProfileLipschitz : ℝ) ≤ ρphysical →
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S (fun _ => 0))) ≤ ρphysical →
    0 ≤ Pphysical → (Mk : ℝ) ≤ Real.exp Pphysical →
    (period : ℝ) ≤ Real.exp (Pphysical ^ 2) →
    (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical → (Fintype.card G : ℝ) ≤ Pphysical →
    (Fintype.card (Fin nX) : ℝ) ≤ Pphysical → Dphysical ≤ Real.exp Pphysical →
    W ≤ Dphysical * S.value →
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
    ∀ (hξn : 0 < ξn),
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
    ∀ {C₀ δspatial fineMesh : ℝ},
    0 < ρphysical → 1 ≤ C₀ → (S.value : ℝ) ≤ C₀ → W ≤ C₀ →
    anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρphysical →
    0 ≤ δspatial →
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S (fun _ => 0)) ≤ δspatial * ρphysical →
    0 < fineMesh →
    Real.exp Pmass * (24 * (probabilityProfileLipschitz : ℝ) *
      Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) / ρphysical) ≤ normalizedSpatialShare coarseTarget / 2 →
    allocatedTupleSpatialError (Fintype.card (Fin nX)) selection
      (PrincipalTupleIndex B (layerSamplerDegree I n)) Mk period C₀ ρphysical ξn W δspatial fineMesh *
      coarseReferenceMassConstant (s + 1) (Fin nX) W S.value ≤ normalizedSpatialShare coarseTarget / 2 →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Pphysical →
    W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) →
    fineMesh ≤ allocatedEarlyRecenteredMesh (Fin nX) selection Mk period Pphysical Ecoarse →
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
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), bases.Nonempty →
    gain ≤ ((wholeLaw).complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S
      (Fin nX) poly hmem N (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW
      hτ hξn stride cells hZ bases x y signal)).re →
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
