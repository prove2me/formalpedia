-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_constructed_finite_source_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_constructed_finite_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:50:23.897658+00:00
-- url     : https://prove2.me/theorems/0d16aa08-71ef-48c5-ac40-2ee39ea77f3d
-- title:
--   A constructed finite chart-model source for the canonical slice
-- statement:
--   Fix the section data (with universe levels $u_J, u_Q, u_X$): a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$, $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L_S = $ `S.value`; a natural number $\mathrm{dim}$, with row sets $\mathrm{rowSets}_j = $ `boundedBooleanJetRows (Fin dim) (j+1)` (subsets of size at most $j+1$), row types $\mathrm{selectedRows}_j$ and inclusions $\mathrm{rows}_j$; grid is the predicate `allocatedGridAxis U basis L_S` on axes, Tuple the tuple index over the non-grid axes, and $L$ the side lengths `allocatedPrincipalSides B U basis S` restricted to Tuple; a point $x : G \to $ `IntegerScalarCubeBox (Fin dim) L_S`; a natural number $M_k > 0$, an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ and $hgood$: `GoodScalarKernelTuple selection (1/Mk) Mk x`; a finite type $X_0$ and $\mathrm{stride}_0 : X_0 \to \mathbb N$; a real $P \ge 0$ with $M_k \le e^{P}$, $R_j \le e^{P}$, $R_j^{-1} \le e^{P}$, $\sigma_j^{-1} \le e^{P}$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^{P}$; finite types $Q_j$; $hb$: the $\mathbb Z$-span of $\mathrm{basis}_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $Q_j$; a natural number $d \neq 0$; natural-valued $H_0, \mathrm{step}_0$ and integer-valued $c_0$ on `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H_0 > 0$ and each progression $\{c_0(t) + \mathrm{step}_0(t)k : 0 \le k < H_0(t)\}$ contained in $[0, \texttt{allocatedPrincipalSides B U basis S t})$; $H, \mathrm{step}, c$ their restrictions to Tuple; a natural number $\mathrm{modulus}$ with $hcanonical$: $\mathrm{modulus} = $ `canonicalSlicedModulus selection stride₀ m x` (with $M = M_k$; it equals `residueRefinedPeriod (kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x _ m)) stride₀` when $x$ is a good kernel tuple, and $1$ otherwise); a label $r_0 :$ tuple index $\to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{modulus}$ with $hcell$: positive mass of the tuples with residue label $r_0$ under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀`; wholeLaw $=$ `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ _ hH₀ hsubset₀ modulus r₀ hcell` (a finite probability law on the full tuples `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S)`); the assumption that each $\mathbb Z^{J_j} \cap V_j$ is a full lattice in $V_j$; additively left-invariant probability measures $\nu_j$ on $V_j/(\mathbb Z^{J_j} \cap V_j)$, with jetHaar $= \prod_j\prod_{\mathrm{selectedRows}_j}\nu_j$; compact Borel structures on `CoefficientTorus (LayerSamplerVariables G I n B) U` and `CoefficientTorus (Fin dim) U` with additively left-invariant probability measures $\mu$ and $\mu_{\mathrm{rows}}$; and a finite type $X$ (universe $u_X$) with decidable equality. The theorem includes among its hypotheses $hcanonical$, $\mu_{\mathrm{rows}}$ (unused in the conclusion), $R > 0$, $\sigma > 0$, $M_k > 0$, $hgood$ and the bounds involving $P$.
--
--   Explicit hypotheses: reals $D, \mathrm{target}, P_k, P_\rho, F, Q_{\mathrm{stride}}$ with `AllocatedComparisonDimensions B (Fin dim) selectedRows D`, $P_k \ge 0$, $M_k \le e^{P_k}$, $P_\rho, \mathrm{target}, F, Q_{\mathrm{stride}} \ge 0$, $\mathrm{stride}_0(i) > 0$, $\mathrm{stride}_0(i) \le e^{Q_{\mathrm{stride}}}$ and $\exp(\texttt{allocatedAffineLengthLog m D P Prho Pk target F}((m+1)P_k + |X_0|\,Q_{\mathrm{stride}})) \le L_S$; a function $g$ assigning to every full tuple $y$ a function $g_y :$ `EuclideanJetLayers U selectedRows` $\to \mathbb R$ that is measurable, nonnegative and jetHaar-integrable, such that the push-forward of $\mu$ with density $z \mapsto$ `allocatedCoefficientDensity B U basis hb o hR hσ S` (multiplication-by-$d$ image of $z$ in the coefficient torus) under `euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U basis S 0 x y) (allocatedPhysicalCubeDirections B U basis S x y) rows` equals jetHaar with density $g_y$; reals $\delta, \eta$, $\rho$ assigning to predicates on axes elements of $\mathbb R_{\ge 0}$, and $t \le 1$ with `AllocatedAffineCoveredComparison B rows δ η ρ t htone`, $0 < \rho(\mathrm{grid}) \le 1$, $\sigma_j \le t$, $\mathrm{step}_j > 0$ on Tuple, $\delta > 0$, $\delta^{-1} \le e^{F}$, $\delta L_j \le |\{c_j + \mathrm{step}_j k : 0 \le k < H_j\}|$ on Tuple, $\mathrm{dim} \le m+1$; a full tuple $y_0$ with $\mathrm{wholeLaw}(y_0) > 0$; $T$ with `partitionedIdealRadius (Fin dim) m` $+1 \le T_j$ and $|\texttt{BoundedCoefficientExponent}\dots(j+1)|\cdot 2^{\mathrm{dim}}(\mathrm{dim}+1)^{j+1} \le T_j$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ \mathrm{basis}_j)^{-1}v\| \le C_j\|v\|$ and $C_j(|I_j|+1)T_jR_j \le 1/4$; $\rho(\mathrm{grid})^{-1} \le e^{P_\rho}$; $0 \le \eta \le \exp(-(\mathrm{target} + 1 + D\,m2^{m+1}P_k + 4))$; a natural number $\mathrm{period} \neq 0$ with $\mathrm{period} = $ `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hgood m)` and $\mathrm{period} \mid d$; $\mathrm{siteRadius} \ge 1$ with $(|\mathrm{rowSets}_j|+1)\,|\mathcal P(\mathrm{Fin}\,\mathrm{dim})|\,C_j(|I_j|+1)\,2\,\mathrm{siteRadius}\,R_j \le 1/4$; $C_{\mathrm{forward}}$ with $\|\texttt{normalizedOrthogonalChart}\ V_j\ \mathrm{basis}_j\ v\| \le C_{\mathrm{forward}}(j)\|v\|$; $K \ge R_j^{-1}$; $|\mathrm{rowSets}_j|\,T_j \le \mathrm{siteRadius}$; reals $P_{\mathrm{box}}, V_{\log}, N_{\log}, M_{\log}, \mathrm{baseAmbient} \ge 0$ with $2\,$`allocatedRowSlicedSiteRadius rowSets` $\le e^{P_{\mathrm{box}}}$, `allocatedFullGridNaturalVolume B U basis S rowSets` $\le e^{V_{\log}}$, $\|(\texttt{allocatedProductIdealNormalizer B U basis S rowSets})^{-1}\| \le e^{N_{\log}}$, $(\texttt{layerKernelIndexBound}\ m\ M_k)^{|\texttt{LayerSamplerAxis I n}|}\cdot$`coefficientDeckPeriodCap selectedRows Q period` $\le e^{M_{\log}}$, $V_{\log}, N_{\log}, M_{\log}, |\mathcal P(\mathrm{Fin}\,\mathrm{dim})|, |\texttt{LayerSamplerAxis I n}|, |\Sigma_a\,\mathrm{selectedRows}_{a.1}| \le \mathrm{baseAmbient}$, and $|(\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}) \times (\prod_j Q_j \to \mathbb Z/\mathrm{period})|$, $K$, $\sum_j C_{\mathrm{forward}}(j)|J_j|$, `normalizedSiteCutoffBound`, $d$, $\mathrm{period}$, $\sum_j|\mathrm{rowSets}_j|$, $L_S^{\texttt{layerTailDegree}\ m+1}$ each $\le e^{\mathrm{baseAmbient}}$; $Q_{\mathrm{grid}} \ge 8(|\texttt{layerIntegerPrincipalSlots B (allocatedGridIntegerAxis B U basis S a)}|+1)$ for grid axes $a$; $\delta_g > 0$ with $\delta_g\cdot\texttt{allocatedPrincipalSides}(t) \le H_0(t)$; a natural number $T_g \ge (\mathrm{dim}+1)\,\mathrm{modulus}/\delta_g$; $\mathrm{step}_0 > 0$; $A_g$ a Lipschitz constant of `Real.smoothTransition`; $P_g \ge 1$ with `scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1` $\le P_g$, `scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 modulus` $\le P_g$ and $\mathrm{step}_0(t)\,\mathrm{modulus} \le P_g$; the block-count bounds `positiveModerateSpectrumBlockCount j |rowSets j| ((layerTailDegree m + 1)|rowSets j|)` $\le |B_{(j,\mathrm{inr}\,i)}|$ and `uniformSpectrumBlockCount j |rowSets j| ((j+1)|rowSets j|)` $\le |B_{(j,\mathrm{inr}\,i)}|$; reals $D_g, v_g, w_g, t_g, p_g \ge 0$ with $\mathrm{dim}, j+1, |\mathrm{rowSets}_j|, \texttt{layerTailDegree}\ m+1, |B_{(j,\mathrm{inr}\,i)}|, \#\text{grid axes}, |\texttt{LayerSamplerAxis I n}|, |\Sigma_a\,\mathrm{selectedRows}_{a.1}|, \sum_j|J_j|, \texttt{probabilityProfileLipschitz} \le D_g$, $R_j, R_j^{-1} \le e^{v_g}$, $\delta_g^{-1} \le e^{w_g}$, $T_g \le e^{t_g}$, $|\texttt{BoundedCoefficientExponent}\dots(j+1)| \le e^{v_g}$, $P_g \le e^{p_g}$; $B_{\mathrm{analytic}} \ge D_g \ge 0$ with `normalizedSiteCutoffBound`, $K\sum_j C_{\mathrm{forward}}(j)|J_j|$, $Q_{\mathrm{grid}} \le e^{B_{\mathrm{analytic}}}$; and $P_{\mathrm{num}} \ge 0$ with $|I_j|, n_j, |\texttt{BoundedCoefficientExponent}\dots(j+1)| \le P_{\mathrm{num}}$, $R_j^{-1} \le e^{P_{\mathrm{num}}}$, `mixedDensityCovolumeRatio V_j basis_j` $\le e^{P_{\mathrm{num}}}$.
--
--   Conclusion. Put $\mathrm{ambientQ} = $ `idealSiteLogBudget (card (Σ a, selectedRows a.1)) dim (Pbox + Prho + Vlog + Nlog + Mlog + target)` and $\mathrm{ambientBudget} = $ `affineAmbientPrimitiveBudget baseAmbient ambientQ`. For every natural number $\mathrm{spatialModulus} \neq 0$ and all $\mathrm{stride}, N : X \to \mathbb N$ with $\mathrm{spatialModulus} = \mathrm{period}$ and $\mathrm{modulus} = \mathrm{refined}$, where $\mathrm{refined} = $ `residueRefinedPeriod spatialModulus stride`, let wholeReference be the constant map from labels (tuple index $\to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{refined}$) to $y_0$ and $r = $ `principalResidueLabel refined y₀`. For all reals $W \ge 0$, $\tau, \xi_n, \mathrm{mesh}$, every $\mathrm{base} : X \to \mathbb Z$, every finite set $\mathrm{cells}$ of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride`, all vector polynomials $\mathrm{poly}_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` of total degree at most $j+1$ with coefficients in $U_j$, and every $\mathrm{test} : (X \to (\mathrm{Unit} \oplus \mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z) \to \mathbb C$, with point $=$ `physicalCubeRowSample U d rows poly hmem`, and for all reals $\kappa, \mathrm{lossTarget}, P_{\mathrm{physical}}, D_{\mathrm{physical}}, P_{\mathrm{sample}}, R_{\mathrm{rank}}, S_{\mathrm{stride}}, \varepsilon_{\mathrm{sample}}, \eta_{\mathrm{sample}}, \rho_{\mathrm{physical}}$, every $\mathrm{actual} : (\texttt{JetAmbientIndex selectedRows J} \to \mathbb R/\mathbb Z) \to \mathbb C$ and $L_a, C_a \in \mathbb R_{\ge 0}$, assume:
--
--   - $\mathrm{stride}_i > 0$, $N_i > 0$, $\tau > 0$, $\mathrm{mesh} > 0$, `allocatedPhysicalRootBudget B U basis S 0` $\le W$, $\|\mathrm{test}\| \le 1$;
--   - $\kappa \le \mathrm{Re}\,\mathbb E_{y \sim \mathrm{wholeLaw}}$ `allocatedRecenteredProfileTerm B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test (fun y z => g y z)` $(y)$ (with the $\tau$ and $\xi_n$ above);
--   - $P_{\mathrm{sample}} \ge 0$, $|X|, |\mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \times X| \le P_{\mathrm{sample}}$, $d \le e^{P_{\mathrm{sample}}}$, $0 \le S_{\mathrm{stride}} \le e^{P_{\mathrm{sample}}}$, $\varepsilon_{\mathrm{sample}} > 0$, $1/\tau, 1/\varepsilon_{\mathrm{sample}} \le e^{P_{\mathrm{sample}}}$, $\mathrm{stride}_i \le S_{\mathrm{stride}}$; with $A$ chosen by OpenAI's existence theorem `exists_translated_physical_jet_l1_perturbation m dim`, $\exp((P_{\mathrm{sample}}+A)^A) \le N_i$, `HasLayerSamplingRank (j+1) N R_rank (U j) (poly j)`, $\exp((P_{\mathrm{sample}}+A)^A) \le R_{\mathrm{rank}}$;
--   - $\mathrm{actual}$ is $L_a$-Lipschitz with $\|\mathrm{actual}\| \le C_a$; $\eta_{\mathrm{sample}} > 0$; $|\texttt{CoefficientAmbientIndex (Fin dim) J}| \le P_{\mathrm{sample}}$; $L_a, C_a \le e^{P_{\mathrm{sample}}}$; $\mathrm{ambientBudget} \le P_{\mathrm{sample}}$; $\sum_j|\texttt{BoundedCoefficientExponent (Fin dim) (j+1)}| \le e^{P_{\mathrm{sample}}}$; $\eta_{\mathrm{sample}}^{-1} \le e^{P_{\mathrm{sample}}}$; and $\mathbb E_{v \sim \mathrm{wholeLaw}}\, g_v(y) = \mathrm{actual}(\texttt{coveredJetAmbientTorus U 1 y})$ for every $y$;
--   - with $\mathcal V = $ `narrowTrimmedSpatialWidths W τ ξn N`: $\mathcal V(z) > 0$ for all $z$ and $\sum_z$ `selectedResidueSmoothWeight stride cells 𝒱 z` $> 0$;
--   - $\xi_n \le 1$, $8(1+W)\,\mathrm{stride}_t\,\rho_{\mathrm{physical}} \le \xi_n\tau N_t$, $8\,$`probabilityProfileLipschitz` $\le \rho_{\mathrm{physical}}$, $2\,|\mathrm{Option}(\texttt{LayerSamplerVariables G I n B})|\cdot 2\,$`allocatedPhysicalEntryBudget B U basis S 0` $\le \rho_{\mathrm{physical}}$;
--   - $P_{\mathrm{physical}} \ge 0$, $M_k \le e^{P_{\mathrm{physical}}}$, $\mathrm{spatialModulus} \le e^{P_{\mathrm{physical}}^2}$, $\mathrm{dim}+1, |G|, |X| \le P_{\mathrm{physical}}$, $D_{\mathrm{physical}} \le e^{P_{\mathrm{physical}}}$, $W \le D_{\mathrm{physical}} L_S$, $\mathrm{lossTarget} + $ `coefficientErrorSpatialLog Pphysical` $+ 8 \le \mathrm{target}$, and $\eta_{\mathrm{sample}}, \varepsilon_{\mathrm{sample}} \le e^{-\mathrm{target}}$.
--
--   Then, with $A_{\mathrm{mass}}, A_{\mathrm{analytic}}$ chosen by `exists_allocatedAffineModelMass_budget m dim` and `exists_allocatedAffineAnalytic_budget m dim`, $F_{\mathrm{model}} = m2^{\mathrm{dim}}(P_{\mathrm{num}}+8)(1+4P_{\mathrm{num}}) + |\texttt{LayerSamplerAxis I n}|\,m2^{m+1}P_k + \sum_j|Q_j|\,|\mathrm{selectedRows}_j|\,(m+1)P_k$, $D_{\mathrm{out}} = |\Sigma_a\,\mathrm{selectedRows}_{a.1}|$, $E_g = D_{\mathrm{out}}P_\rho + \mathrm{target} + F_{\mathrm{model}} + 1$, $p = $ `slicedGridGeometryLog Dg vg wg tg` $+ p_g$, $\Lambda_j(E) = $ `slicedGridSiteLog j |rowSets j| ((layerTailDegree m + 1)|rowSets j|) ((j+1)|rowSets j|) Dg p E`, $C_p = \sum_j(\Lambda_j(0) + D_g(v_g+1))$, $E_g' = $ `uniformProductAccuracyLog Dg Cp Eg` $+ D_g(v_g+1) + 1$, $O_p = \sum_j(\texttt{siteExponentialOutputLog}\ |\mathcal P(\mathrm{Fin}\,\mathrm{dim})|\ \Lambda_j(E_g') + (D_g+1)(v_g+1))$, $V_{\mathrm{grid}} = e^{O_p}$, $\Xi = D_g + p + v_g + F_{\mathrm{model}} + P_\rho + P_k + \mathrm{target}$:
--
--   there exists $e$ assigning to each grid axis a `ScalarSiteExpansion (Finset (Fin dim))` with `(e a).Bounds` $(e^{O_p}, e^{O_p}, e^{O_p}, e^{O_p}, e^{\texttt{slicedGridGeometryLog Dg vg wg tg} + D_g + v_g + 8})$, and there exist a natural number $k$, $a : K \to \mathbb C$ and $f : K \to \mathcal P(\mathrm{Fin}\,\mathrm{dim}) \to (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$ for $K = (\mathcal P(\mathrm{Fin}\,\mathrm{dim}) \times \texttt{LayerSamplerAxis I n} \to \mathrm{Fin}\,k)$, such that
--
--   - $\sum_{\mathrm{label}}\sum_i\sum_{k_g}\|2^{|\mathcal P(\mathrm{Fin}\,\mathrm{dim})|}\cdot$ `allocatedProductMaskedIdealCoefficient B U basis S rowSets x y₀ modulus d period a label i` $\cdot$ `coverSiteCoefficient e kg`$\| \le \exp((\Xi + A_{\mathrm{mass}})^{A_{\mathrm{mass}}})$ (labels range over $\mathcal P(\mathrm{Fin}\,\mathrm{dim}) \to (\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}) \times (\prod_j Q_j \to \mathbb Z/\mathrm{period})$, $k_g$ over choices of one term of each `e a`);
--   - there exists $L_{\mathrm{an}} \in \mathbb R_{\ge 0}$ with $L_{\mathrm{an}}\cdot\mathrm{period}\cdot V_{\mathrm{grid}}^{\#\text{grid axes}} \le \exp((\Xi + B_{\mathrm{analytic}} + A_{\mathrm{analytic}})^{A_{\mathrm{analytic}}})$ and $\mathrm{period}\cdot(e^{O_p})^{\#\text{grid axes}} \le$ the same bound, and a complex-valued analyticFactor of (label, $i \in K$, $k_g$, site, point of $\bigl((\texttt{JetAmbientIndex (fun _ => Unit) J} \to \mathbb R/\mathbb Z) \times (\Sigma_j J_j \to \mathbb R/\mathbb Z)\bigr) \times (\Sigma_j J_j \to \mathbb R/\mathbb Z)$), each $L_{\mathrm{an}}$-Lipschitz in the point and of norm $\le 1$, with `AllocatedModelPhysicalExpansionIdentity B U basis S x y₀ modulus d period siteRadius _ hb o bW e a f poly hmem analyticFactor` (OpenAI's identity expanding the chart model at every physical row sample into products of these factors);
--   - and
--   $$\kappa - e^{-\mathrm{lossTarget}} \le \mathrm{Re}\sum_{(c, w) \in \mathrm{cells} \times \texttt{spatialWindow Hsp 4}} \omega_c\,\rho_{c,w}\,\Phi(Y_{c,w})\,\Gamma(Y_{c,w}),$$
--   where $H_{sp} = $ `trimmedSpatialRootScale τ N stride`, $\omega_c = $ `selectedResidueCellWeight stride cells 𝒱 c`, $\rho_{c,w} = $ `allocatedRecenteredResidueWeight B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells test r c w`, $Y_{c,w} = \mathrm{point}(\texttt{allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r c w})$, $\Phi = $ `allocatedProductChartIdealApproximation B U basis S rowSets x y₀ modulus d period siteRadius _ hb o bW a f` and $\Gamma = $ `allocatedFullGridChartModel B U basis S rowSets d hb o bW e`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_constructed_finite_source_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_constructed_finite_source` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedFiniteSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B213`, `OAIE3v2B216` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedFiniteSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_constructed_finite_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213
import Definitions.Def_OAIE3v2B216

section

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
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
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
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
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
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype dim (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin dim) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

include hcanonical μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in

theorem exists_allocatedCanonicalSlice_constructed_finite_source_s2
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
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U basis S tg ≤ (H₀ tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin dim) + 1) * modulus : ℕ) : ℝ) / δg ≤ Tg)
    (hstepAll : ∀ tg, 0 < step₀ tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 modulus ≤ Pg)
    (hstrideGrid : ∀ tg, ((step₀ tg * modulus : ℕ) : ℝ) ≤ Pg)
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
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin dim))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    let _center := principalProgressionSliceCenter (α := (Fin dim)) activeB activeDegree L c
    let _width := principalProgressionSliceWidth (α := (Fin dim)) activeB activeDegree L H step
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
    ∀ {κ lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → 0 < τ → 0 < mesh →
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    (∀ v, ‖test v‖ ≤ 1) →
    κ ≤ ((wholeLaw).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξn)
      B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test
      (fun y z => (g y z : ℂ)))).re →
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
    let Hsp := trimmedSpatialRootScale τ N stride
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
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
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m dim)
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m dim)
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin dim)) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let Dout := (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ)
    let Eg := Dout * Prho + (target + Fmodel) + 1
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let LgridLog := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) Dg p e
    let Cp := ∑ j, (LgridLog j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (LgridLog j Eg') + (Dg + 1) * (vg + 1))
    let Vgrid : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg Op⟩
    ∃ e : {a // grid a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
    ∃ k : ℕ, ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
      (f : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U basis S rowSets x y₀ modulus d period a label i) *
            coverSiteCoefficient e kg‖) ≤
          Real.exp ((Dg + p + vg + Fmodel + Prho + Pk + target + Amass) ^ Amass) ∧
        (∃ Lanalytic : ℝ≥0,
          ((Lanalytic * ((period : ℝ≥0) * Vgrid ^ Fintype.card {a // grid a}) : ℝ≥0) : ℝ) ≤
            Real.exp ((Dg + p + vg + Fmodel + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic) ∧
          (period : ℝ) * (Real.exp Op) ^ Fintype.card {a // grid a} ≤
            Real.exp ((Dg + p + vg + Fmodel + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic) ∧
          ∃ analyticFactor : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period))) →
              (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → (∀ a, (e a).Term) → Finset (Fin dim) →
              (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
                ((Σ j, J j) → UnitAddCircle)) → ℂ,
            (∀ label i kg t, LipschitzWith Lanalytic (analyticFactor label i kg t)) ∧
            (∀ label i kg t z, ‖analyticFactor label i kg t z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U basis S x y₀ modulus d period siteRadius (zero_lt_one.trans_le hrone) hb o bW e a f poly hmem analyticFactor) ∧
    κ - Real.exp (-lossTarget) ≤
      (∑ t : cells × spatialWindow (α := Fin dim) Hsp 4, (selectedResidueCellWeight stride cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U basis S X spatialModulus stride wholeReference x hMk selection hgood
          N hW mesh base cells test r t.1 t.2.val *
        (allocatedProductChartIdealApproximation B U basis S rowSets x y₀ modulus d period siteRadius
            (zero_lt_one.trans_le hrone) hb o bW a f (point (allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r
          t.1.val t.2.val)) *
          allocatedFullGridChartModel B U basis S rowSets d hb o bW e
            (point (allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r
              t.1.val t.2.val)))).re := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
