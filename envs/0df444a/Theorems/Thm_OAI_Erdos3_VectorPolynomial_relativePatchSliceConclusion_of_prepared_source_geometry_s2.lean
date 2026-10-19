-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_relativePatchSliceConclusion_of_prepared_source_geometry_s2
-- name    : OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_prepared_source_geometry_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:08:48.759276+00:00
-- url     : https://prove2.me/theorems/a59fb370-95c6-4422-a81d-24e38b73fb5e
-- title:
--   From prepared source geometry and a normalized candidate conclusion to a relative patch slice conclusion
-- statement:
--   This is a technical assembly step in OpenAI's argument with a long list of hypotheses. All named functions, structures and predicates below are defined by OpenAI; the many explicit logarithmic budgets (`preparedConcreteSlicedForecastNativeLog`, `preparedConcreteSlicedForecastMassLog`, `preparedConcreteSlicedForecastCapLog`, `preparedSlicedForecastSourceLog`, and so on) are explicit real-valued functions of the displayed parameters.
--
--   **Data.** Let $m, M, n_X, J_{\mathrm{alloc}}$ be natural numbers and $J_0$ a type. Let `prep` be a `RankPreparationFamily (Fin nX) J₀ m` (a family of $m$ rank-preparation layers; layer $j$ has a finite coordinate type $\mathrm{Coord}_j$, a subspace $V_j$ = `(prep j).space` of $\mathrm{Coord}_j \to \mathbb{R}$, a vector polynomial `(prep j).poly` and a rank `(prep j).rank`), satisfying `prep.PreparedHeights preparationP Rprep` for reals/naturals with $0 \le \mathrm{preparationP}$ and $1 \le \mathrm{Rprep}$. Write $\mathcal{K}$ = `EnlargedPreparedCommonKernel m Jalloc` $= \mathrm{Fin}((m+1)(m+3) + (m+1)J_{\mathrm{alloc}})$, $\mathcal{I}_j = \mathrm{Fin}((\texttt{prep}\ j).\mathrm{rank})$, $t_j$ = `preparedSamplerTransverse prep j` (the dimension of the orthogonal complement of `euclideanSubspace` $V_j$), $\mathcal{B}$ = `EnlargedPreparedCommonSamplerBlock prep Jalloc`, and $\mathrm{Vars}$ = `LayerSamplerVariables 𝒦 𝓘 t 𝓑`. Let $E_{\mathrm{out}}$ be a family of finite types indexed by $\mathrm{Fin}\ m$; $b_j$ a basis indexed by $\mathrm{Fin}\ t_j$ of the orthogonal complement of `euclideanSubspace` $V_j$ whose $\mathbb{Z}$-span is `projectedIntegerLattice` of that subspace (hypothesis $hb$); $o_j$ an orthonormal basis of `euclideanSubspace` $V_j$ indexed by $\mathcal{I}_j$; $bW_j$ a $\mathbb{Z}$-basis indexed by $E_{\mathrm{out}}\ j$ of the lattice $\Lambda_j$ = `latticeSection (standardEuclideanLattice Coord_j) (euclideanSubspace V_j)`, assumed to be a $\mathbb{Z}$-lattice; $\nu_j$ a left-invariant probability measure on `euclideanSubspace` $V_j / \Lambda_j$; and assume `EuclideanJetLayers V (fun _ => Unit)` is compact. Let $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$; $S$ a `LayerSamplerScale 𝓑 V b R σ` with kernel variables $\mathcal{K}$; $L_{\mathrm{rank}} \in \mathbb{N}$ and embeddings `spatial` $: \mathrm{Fin}\ L_{\mathrm{rank}} \hookrightarrow \mathcal{K}$, `kernel j` $: \mathrm{Fin}\ L_{\mathrm{rank}} \times \mathrm{Fin}(j+1) \hookrightarrow \mathcal{K}$, and `block j a` $: \mathrm{Fin}\ L_{\mathrm{rank}} \hookrightarrow \mathcal{B}\langle j, a\rangle$ for the active axes $a$ (with respect to `allocatedShortAxis V b S.value`); an embedding $e_{\mathrm{Spatial}} : \mathrm{Fin}\ 2 \times \mathrm{Fin}\ n_X \hookrightarrow \mathcal{K}$; reals $\mathrm{gainLog}, \xi, \mathrm{cost}$; $N, \mathrm{stride} : \mathrm{Fin}\ n_X \to \mathbb{N}$; a finite set `cells` of column residue patterns modulo `stride`; a point `center` of the coefficient torus; and an `AllocatedExternalCandidateSampler 𝓑 V b S hb o hR hσ N (prep ·).poly _ (exp(-(gainLog + nX + 8))) ξ stride cells center` $A$ (a candidate sampler with sites, paths, a law `A.law`, sides `A.sides`, widths `A.widths`). Let $\mathrm{degree}, \mathrm{originalRank}, D, E$ be natural numbers, $f : (\mathrm{Fin}\ n_X \to \mathbb{Z}) \to \mathbb{R}$, $\lambda$ real, reals $\mathrm{chartCost}, \mathrm{childCost}, \mathrm{gain}, p_{\mathrm{Global}}$, a natural number $\mathrm{netExponent}$, and a finite set `productive` of paths of $A$. Let $\kappa$ be the natural number chosen via `Classical.choose` from OpenAI's theorem `exists_relative_finite_returned_fiber_normalization degree`, and put $Z = \bigl((\mathrm{childCost} + |\mathrm{Vars}| + 2) + 2\bigr)^{\kappa}$.
--
--   **Hypotheses (first group).** $0 \le \mathrm{childCost}$; $e^{-\mathrm{gainLog}} \le \mathrm{gain}$; $\mathrm{gain}/16 <$ `A.law.mass productive`; $(Z + 2)^{\texttt{allocatedNormalizedShearObservableExponent degree}} \le p_{\mathrm{Global}}$; $0 \le p_{\mathrm{Global}}$; $\mathrm{chartCost} \le p_{\mathrm{Global}}$; $Z \le p_{\mathrm{Global}}$; $\mathrm{gainLog} + 16 + (\mathrm{degree} + 1)\,\mathrm{childCost} + Z \le p_{\mathrm{Global}}$; $f(x) \in [0, 1]$ for all $x$; $\lambda \in [0, 1]$; and `A.DegreeGlobalizationAt (fun x => f x - λ) degree netExponent pGlobal cost` holds (with output types $E_{\mathrm{out}}$).
--
--   **Hypotheses (second group).** Let $p_{\mathrm{Radius}}, Q_{\mathrm{stride}}, P_F, P_{\mathrm{chart}}, \mathrm{childLog}, P_{\mathrm{dim}}$ be reals, and write $\mathrm{NL}(y)$, $\mathrm{ML}(y)$, $\mathrm{CL}$ for `preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog y`, `preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog y` and `preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog`, and $\mathrm{SL}$ for `preparedSlicedForecastSourceLog m M Jalloc Ptest`. Suppose:
--   1. $0 < m$; $|\mathrm{Coord}_j| \le M$ for all $j$; $p_{\mathrm{Radius}}, \mathrm{gainLog}, Q_{\mathrm{stride}}, P_F, P_{\mathrm{chart}}, \mathrm{cost} \ge 0$.
--   2. `mixedDensityCovolumeRatio (euclideanSubspace V_j) (b j)` $\le e^{P_{\mathrm{chart}}}$, $R_j \le 1$, $R_j^{-1} \le e^{p_{\mathrm{Radius}}}$ and $\sigma_j \le 1$ for all $j$.
--   3. $\mathrm{forward} : \mathrm{Fin}\ m \to \mathbb{R}_{\ge 0}$ with $\lVert \phi_j(w) \rVert \le \mathrm{forward}_j \lVert w \rVert$ and $\mathrm{forward}_j \le e^{P_F}$, and $\mathrm{inverse} : \mathrm{Fin}\ m \to \mathbb{R}$ with $\mathrm{inverse}_j \ge 0$ and $\lVert \phi_j^{-1}(w) \rVert \le \mathrm{inverse}_j \lVert w \rVert$, where $\phi_j$ = `normalizedOrthogonalChart (euclideanSubspace V_j) (b j)`.
--   4. For a natural number $C_{\mathrm{detect}}$ and reals $B_{\mathrm{struct}}, P_{\mathrm{scale}}, D_{\mathrm{geometry}}, \mathrm{target}, P_k, P_\rho, p_{\mathrm{Detect}}, a_{\mathrm{Detect}}, \mathrm{detectionGain}$: $\mathrm{inverse}_j \le e^{B_{\mathrm{struct}}}$ for all $j$, and `PreparedUniformDegreeGeometryAt 𝓑 V b S 0 Cdetect nX Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain` holds.
--   5. $0 \le \mathrm{childLog}$; `centerLift j` $\in V_j$ for each $j$; and `AllocatedNormalizedCandidateConclusion degree (fun k => preparedSlicedForecastChildSize childLog ≤ A.sides k) centerLift productive childCost chartCost (originalRank + degree·E) f λ` holds (for the sampler $A$ and output types $E_{\mathrm{out}}$).
--   6. $\xi \le 1$ and $2\cdot$`spatialTrimMargin (exp(-(gainLog + nX + 8))) N x` $\le N(x)$ for all $x$.
--   7. Reals $u, p, p_{\mathrm{Slice}}, p_{\mathrm{Test}}, \mathrm{localBudget}, \mathrm{precision}, C, E_{\mathrm{compare}}, P_{\mathrm{test}}, R_{\mathrm{rank}}, C_{\mathrm{recovered}}$ with $u \ge 0$, $p \ge 0$, $\mathrm{localBudget} \ge 0$, $p_{\mathrm{Slice}}\,|\mathrm{Vars}| \le p$, $1 \le C \le e^{p}$, $\mathrm{CL} \le p$, and `actualForecastDataModelRequired localBudget (NL(2u + 4p + 12)) (ML(2u + 4p + 12)) u p` $\le \mathrm{precision}$.
--   8. `A.NativeDetection 0 pSlice pTest localBudget (forecastAugmentedUnitThreshold u p (exp(pSlice·|Vars|)) C (exp CL))` holds, and the excess mass of `A.law.siteLaw (A.physicalBox _ _)` over $C$ times the uniform weights on `integerBox N` (i.e. $\sum_x \max(q_x - C p_x, 0)$) is at most $6\cdot$`positiveProjectionAccuracy precision`.
--   9. $0 \le p_{\mathrm{Slice}}$, $\mathrm{cost} \le p_{\mathrm{Slice}}$, $\mathrm{chartCost} \le p_{\mathrm{Slice}}$, $2 \le p_{\mathrm{Test}}$; an equivalence $\mathrm{Fin}(\mathrm{tagCount}) \simeq$ `prep.PreparedCoordinate`; $\mathrm{cost} + \mathrm{cost} + 6 \le u$.
--   10. $\max\bigl(\max(\mathrm{localBudget}, 3\,\mathrm{NL}(2u + 4p + 12) + 3),\ 2u + 4p + \max(0, \mathrm{ML}(2u + 4p + 12)) + 20\bigr) + 2 + \mathrm{cost} + \mathrm{cost} + 8 \le E_{\mathrm{compare}}$, and $\max(\mathrm{localBudget}, 3\,\mathrm{NL}(2u + 4p + 12) + 3) \le P_{\mathrm{test}}$.
--   11. $|\sigma_j| \le \exp\bigl(-\texttt{fixedPathSlicedPerturbationLog}\ D_c\ (D_c + \mathrm{SL} + 4)\ (\mathrm{cost} + 1)\ (2\,\mathrm{SL} + (E_{\mathrm{compare}} + 4) + 14)\ m\bigr)$ for all $j$, where $D_c$ = `allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc)`.
--   12. With $k$ = `nativeForecastAmbientExponent m` and $Y = \max\bigl(\max(\texttt{preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost},\ 2\max(P_{\mathrm{test}}, 3\,\mathrm{NL}(E_{\mathrm{compare}} + 8) + 3) + 1),\ \mathrm{ML}(E_{\mathrm{compare}} + 8) + E_{\mathrm{compare}} + 8\bigr)$: $\exp((Y + k)^{k}) \le N(i)$ for all $i$, $\exp((Y + k)^{k}) \le R_{\mathrm{rank}}$, and `HasLayerSamplingRank (j + 1) N R_rank V_j (prep j).poly` for all $j$.
--   13. Functions `sampleFn` (from a base point and a frame to `CoefficientSamplerArrays`) and `readFn` (from a base point and a frame to integer readouts on `AllocatedActualCoefficientIndex 𝒦 (Fin nX) 𝓘 Eout t 𝓑`) such that `AllocatedCenteredRecoveredSampleReadAt 𝓑 V bW b hb o S hR hσ (prep ·).poly _ short spatial kernel block Crecovered center centerLift base (sampleFn base) (readFn base)` holds for every `base`, and `AllocatedCenteredFramedRecoveredSampleAt 𝓑 V b hb o S hR hσ (prep ·).poly _ centerLift z₁ z₂ (sampleFn z₁ z₂) (allocatedJointFrameRead z₁ (readFn z₁ z₂))` holds for every $z = (z_1, z_2) \in$ `productive`.
--   14. With `primes` = `boundedPrimes ⌈exp(2 Ptest)⌉₊`, for every $z \in$ `productive`, $\prod_{p \in \mathrm{primes}} p^{\texttt{largestTestedBadDepth}(\ldots)(p)} \le (\prod_x \mathrm{stride}(x))^2\cdot(\texttt{smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)}\cdot\texttt{quantitativeBadPrimeRadius (gainLog + 8)})$, where the bad depths are those of `allocatedActualPrimeBad short spatial kernel block primes (modularForecastRankConstant m (nX + m M))` at the read data of $z$, tested up to $\log_p \lceil e^{2P_{\mathrm{test}}} \rceil$.
--   15. For every $z \in$ `productive` and $t \in \mathrm{Fin}\ 2$: `spatialMatrixBlockThreshold nX (jointSpatialError gainLog)` $/2 < |\det(i, j \mapsto \texttt{spatialMatrixNormalizedEntries eSpatial A.widths z₂ (t, j, i)})|$.
--   16. $0 \le P_{\mathrm{dim}}$, $n_X \le P_{\mathrm{dim}}$, $|\mathrm{Vars}| \le P_{\mathrm{dim}}$, $0 < n_X$, $\mathrm{gainLog} \le P_{\mathrm{dim}}$, $\mathrm{stride}(x) \le e^{Q_{\mathrm{stride}}}$ for all $x$, $0 \le E_{\mathrm{compare}}$.
--   17. `preparedSlicedForecastCommonFloor 0 childLog cost (preparedSlicedForecastComparisonFloorLog m M nX Jalloc (nX + m M + |Σ j, 𝓘 j|) Pdim cost pRadius gainLog Qstride Ptest (2 Ptest) Ecompare)` $\le$ `S.value`; $\xi \le \exp(-(2\,\mathrm{SL} + (E_{\mathrm{compare}} + 4) + 14))$; and $\exp\bigl(\texttt{forecastJointGridAmbientLog}\ (n_X + mM + |\Sigma_j \mathcal{I}_j|)\ (\texttt{preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest})\ (E_{\mathrm{compare}} + 4)\ (2P_{\mathrm{test}})\ (\mathrm{gainLog} + n_X + 8)\bigr) \le N(i)$ for all $i$.
--   18. $|\mathrm{Coord}_j| \le \mathrm{preparationP}$ for all $j$, and $\lVert bW_j(a) \rVert \le \exp((\mathrm{preparationP} + 2)^{\texttt{preparedIntegralBasisExponent m}})$ for all $j, a$.
--   19. Reals $\varepsilon, \mathrm{crtBudget}$ with $0 < \varepsilon \le 1$, $1 \le \mathrm{crtBudget}$, $\varepsilon^{-1} \le \mathrm{crtBudget}$, and $P_{\mathrm{test}}$, `preparedSlicedForecastBadLog m nX Qstride gainLog`, $\mathrm{cost} + 1$ all in $[0, \mathrm{crtBudget}]$.
--   20. $m \le \mathrm{degree}$ and $\sum_j (\texttt{prep}\ j).\mathrm{rank} \le mD$.
--   21. A real $\mathrm{budget}$ with $1 \le \mathrm{budget}$, $\mathrm{childCost} + \mathrm{degree}\cdot D \le \mathrm{budget}$, $n_X + mM \le \mathrm{budget}$, $2048\,\mathrm{crtBudget}^3 + (\mathrm{preparationP} + 2)^{\texttt{preparedIntegralBasisExponent m} + 1} \le \mathrm{budget}$, $2Z + 1 \le \mathrm{budget}$, $\mathrm{CL} \le \mathrm{budget}$, $\mathrm{NL}(2u + 4p + 12) \le \mathrm{budget}$, $\mathrm{cost} \le \mathrm{budget}$, and $\exp(\texttt{spatialPatchExtractionCost (recoveredKernelScalarBudget budget)}) \le N(i)$ for all $i$.
--
--   **Conclusion.** `RelativePatchSliceConclusion degree N f ((1 - ε) λ) (originalRank + degree·(D + E)) c` holds, where $c$ = `spatialPatchExtractionCost (recoveredKernelScalarBudget budget)`. By OpenAI's definition this means: there are a positive integer $q$, a residue box slice $S'$ of the box $N$ with modulus $q$, a natural number $d \le \mathrm{originalRank} + \mathrm{degree}\,(D + E)$ and a `PolynomialPatch (Fin nX) degree d` $A'$ such that every side length of $S'$ is at least $e^{-c} N(i)$, `relativePatchComplexity A'` $\le c$, and $e^{-c} \le$ `relativePatchSliceScore S' f ((1 - ε) λ) A'`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_prepared_source_geometry_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_prepared_source_geometry` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedSourceGeometryNormalizedPatchConclusion.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B304`, `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedSourceGeometryNormalizedPatchConclusion.lean (declaration OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_prepared_source_geometry)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B266

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m M nX Jalloc : ℕ} {J₀ : Type}
variable (prep : RankPreparationFamily (Fin nX) J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m Jalloc)) (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Lrank : ℕ} {spatial : Fin Lrank ↪ (EnlargedPreparedCommonKernel m Jalloc)}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ (EnlargedPreparedCommonKernel m Jalloc)}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ (EnlargedPreparedCommonSamplerBlock prep Jalloc) ⟨j,a.val⟩}
variable (eSpatial : Fin 2 × (Fin nX) ↪ (EnlargedPreparedCommonKernel m Jalloc))
variable {gainLog : ℝ}
variable {N : (Fin nX) → ℕ} {ξ cost : ℝ}
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : (Fin nX) → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc))) (Fin nX) stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  (Real.exp (-(gainLog + (nX : ℝ) + 8))) ξ stride cells center}

local instance instNonemptySiteEnlargedPreparedCommonKernelFinPreparedSamplerContinuousEnlargedPreparedCommonSamplerBlockCoord_rd1f114_1 : Nonempty A.Site := A.site_nonempty
variable {degree originalRank D E : ℕ}
variable (f : ((Fin nX) → ℤ) → ℝ) (lam : ℝ)
variable {chartCost childCost : ℝ} {productive : Finset A.Path}
variable {gain pGlobal : ℝ} {netExponent : ℕ}
variable (hchild : 0 ≤ childCost)
  (hgain : Real.exp (-gainLog) ≤ gain)
  (hReady : gain / 16 < A.law.mass productive)
  (hregularityBudget : ((((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 2) ^
    allocatedNormalizedShearObservableExponent degree ≤ pGlobal)
  (hpGlobal : 0 ≤ pGlobal) (hchartGlobal : chartCost ≤ pGlobal)
  (hscoreGlobal : (((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hmassGlobal : gainLog + 16 + ((degree : ℝ) + 1) * childCost + (((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hfGlobal : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
  (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
  (rule : A.DegreeGlobalizationAt (E := Eout) (fun x => ((f x - lam : ℝ) : ℂ))
    degree netExponent pGlobal cost)
variable {pRadius Qstride PF Pchart childLog Pdim : ℝ}

include ν hpPrep hRprep hchild hgain hReady hregularityBudget
  hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule in

theorem relativePatchSliceConclusion_of_prepared_source_geometry_s2

    (hmPositive : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace ((prep j).space)) (b j) ≤ Real.exp Pchart)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (prep j)), ‖normalizedOrthogonalChart (euclideanSubspace ((prep j).space)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace ((prep j).space) × (Fin (preparedSamplerTransverse prep j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace ((prep j).space)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
    (hchildLog : 0 ≤ childLog)

    (centerLift : ∀ j, (prep j).space)
    (hinit : AllocatedNormalizedCandidateConclusion (E := Eout) (A := A)
      degree (fun k => (preparedSlicedForecastChildSize childLog) ≤ A.sides k) centerLift productive childCost chartCost
      (originalRank + degree * E) f lam)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin (Real.exp (-(gainLog + (nX : ℝ) + 8))) N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : (preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog) ≤ p)
    (hPrecision : actualForecastDataModelRequired localBudget (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) (preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (2 * u + 4 * p + 12)) u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)))) C (Real.exp (preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog))))
    (hexcess : letI : DecidableEq (Fin nX) := Classical.decEq _
      letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    (hU : cost + cost + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) + 3))
        (2 * u + 4 * p + max 0 (preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (2 * u + 4 * p + 12)) + 20) + 2 +
      cost + cost + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)) ((allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)) + (preparedSlicedForecastSourceLog m M Jalloc Ptest) + 4) (cost + 1)
      (2 * (preparedSlicedForecastSourceLog m M Jalloc Ptest) + (Ecompare + 4) + 14) m))
    (hlarge : ∀ i, Real.exp ((max (max (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost) (2 * max Ptest (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8)) + 3) + 1))
      ((preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)) + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost) (2 * max Ptest (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8)) + 3) + 1))
      ((preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)) + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : ((Fin nX) → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) × (Fin nX) → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
    (readFn : ((Fin nX) → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) × (Fin nX) → ℤ) →
      AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m Jalloc) (Fin nX) (PreparedSamplerContinuous prep) Eout (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc) → ℤ)
    (hglobal : ∀ base, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space)
      bW b hb o S hR hσ (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) (fun j : Fin m => (prep j).space) b S.value)
      spatial kernel block Crecovered center centerLift base (sampleFn base) (readFn base))
    (hrecovered : ∀ z ∈ productive, AllocatedCenteredFramedRecoveredSampleAt
      (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      centerLift z.1.val z.2.val (sampleFn z.1.val z.2.val)
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val)))
    (hgood : let primes := boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊
      letI := actualForecastPrimeNeZero primes (boundedPrimes_prime _)
      ∀ z ∈ productive,
      (∏ p ∈ primes, p ^ largestTestedBadDepth (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
        (allocatedActualPrimeBad (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) (fun j : Fin m => (prep j).space) b S.value)
          spatial kernel block primes (modularForecastRankConstant m (nX + m * M) : ℝ)) p
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val))) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hdet : ∀ z ∈ productive, ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card (Fin nX)) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : (Fin nX) => spatialMatrixNormalizedEntries eSpatial A.widths z.2.val (t,j,i))|)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card (Fin nX) : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card (Fin nX)) (hgainDim : gainLog ≤ Pdim)
    (hstrideSource : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hE : 0 ≤ Ecompare)
    (hSourceFloor : preparedSlicedForecastCommonFloor 0
      childLog cost (preparedSlicedForecastComparisonFloorLog m M nX Jalloc
        ((nX + m * M) + Fintype.card (Σ j, (PreparedSamplerContinuous prep) j)) Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare) ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * (preparedSlicedForecastSourceLog m M Jalloc Ptest) + (Ecompare + 4) + 14)))
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      ((nX + m * M) + Fintype.card (Σ j, (PreparedSamplerContinuous prep) j))
      (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest)
      (Ecompare + 4) (2 * Ptest) (gainLog + nX + 8)) ≤ (N i : ℝ))
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    {ε crtBudget : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hCRTbudget : 1 ≤ crtBudget) (hCRTinv : ε⁻¹ ≤ crtBudget)
    (hCRTtest : Ptest ∈ Set.Icc 0 crtBudget)
    (hCRTbad : (preparedSlicedForecastBadLog m nX Qstride gainLog) ∈ Set.Icc 0 crtBudget)
    (hCRTpres : (cost + 1) ∈ Set.Icc 0 crtBudget)
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * D)
    {budget : ℝ}
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : childCost + (degree : ℝ) * D ≤ budget)
    (hDmodBudget : ((nX + m * M) : ℝ) ≤ budget)
    (hMatrixBudget : 2048 * crtBudget ^ 3 + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : 2 * (((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget)
    (hcapLog : (preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog) ≤ budget) (hPnative : (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) ≤ budget)
    (hScoreBudget : cost ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (originalRank + degree * (D + E))
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
