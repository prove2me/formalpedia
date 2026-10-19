-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:19:32.968986+00:00
-- url     : https://prove2.me/theorems/2bb9208e-be7d-41b8-aa6a-9799b11ab449
-- title:
--   Shared-width direct detection in the prepared modular general ambient yields a native twist
-- statement:
--   **Section data.** Natural numbers $m, s$; a finite type $G$ with decidable equality; finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$ with proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$; a `LayerSamplerScale` $S$ for $(B, U, \mathrm{basis}, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a natural number $n_X$; an embedding $\mathrm{selection} : \mathrm{Fin}(s+1) \hookrightarrow G$; $\mathrm{stride}, N : \mathrm{Fin}\,n_X \to \mathbb N$ with all $N_i \ne 0$; a polynomial $P_{\mathrm{detect}} \in \mathbb N[x]$; reals $u, p_{\mathrm{model}}, p_{\mathrm{slice}}$; $V_{\mathrm{tail}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$; a real $\alpha$; a real $P$; finite types $Q_j$; a proof $hb$ that the $\mathbb Z$-span of $\mathrm{basis}_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$, indexed by $Q_j$, of the lattice sections `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (assumed to be `IsZLattice`); left-invariant probability measures $\nu_j$ on the quotients of `euclideanSubspace (U j)` by these sections; a compact Borel structure and a left-invariant probability measure $\mu$ on `CoefficientTorus (K := Vars) U` with $\mathrm{Vars} =$ `LayerSamplerVariables G I n B`; the same, $\mu_{\mathrm{rows}}$, on `CoefficientTorus (K := Fin (s+1)) U`; and a Borel structure on `SiteTorus (Finset (Fin (s+1))) U`. Write $p_D = q_D =$ `allocatedModelTestLog u pModel` $= 2u + 5p_{\mathrm{model}} + 12$, $M_k =$ `allocatedDetectedKernelCutoff s G |Vars| Pdetect p_D q_D α` and $g =$ `allocatedDetectedGain s |Vars| Pdetect p_D q_D α` (a natural number and a real defined by OpenAI), and $\mathrm{rows}_j =$ `boundedBooleanJetRows (Fin (s+1)) (j+1)`.
--
--   **Hypotheses, in order.** $s \le m$. Reals $P_{\mathrm{chart}}, D, \mathrm{target}, P_k, P_\rho, Q_{\mathrm{stride}}$ and $K \in \mathbb R_{\ge 0}$ with an `AllocatedEarlyNativeSourceGeometryGeneral Pchart P D target Pk Prho Qstride p_D K` (a structure bundling bounds on $R, \sigma$, cardinalities, the scale $S.\mathrm{value}$, auxiliary radii $\rho$, a tolerance $t$ and an `AllocatedAffineCoveredComparison`). Reals $P_{\mathrm{master}} \le P_{\mathrm{late}}$ with $0 \le P_{\mathrm{master}}$, $D \le P_{\mathrm{master}}$, $P_k, Q_{\mathrm{stride}}, p_D \in [0, P_{\mathrm{master}}]$, $n_X \le P_{\mathrm{master}}$; $R_j \le 1$ and $R_j^{-1} \le e^{P_{\mathrm{master}}}$; $S.\mathrm{value} \le e^{P_{\mathrm{late}}}$; $K \le e^{P_{\mathrm{master}}}$; `normalizedSiteCutoffBound` $\le e^{P_{\mathrm{master}}}$; $M_k \le e^P$ and $M_k \le e^{P_k}$; $\mathrm{stride}_i > 0$ and $\mathrm{stride}_i \le e^{Q_{\mathrm{stride}}}$. $C : \mathrm{Fin}\,m \to \mathbb R$ with $0 \le C_j \le e^{P_{\mathrm{chart}}}$ and $\|\phi_j^{-1}(v)\| \le C_j\|v\|$, and $C^{\mathrm{fw}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\phi_j(v)\| \le C^{\mathrm{fw}}_j \|v\|$ and $C^{\mathrm{fw}}_j \le e^{P_{\mathrm{master}}}$, where $\phi_j$ is `normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)`; $V_{\mathrm{tail},j} \le e^{P_{\mathrm{master}}}$; $0 \le$ `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j)` $\le V_{\mathrm{tail},j}$; and for all $j, i$, both `positiveModerateSpectrumBlockCount j |rows_j| ((layerTailDegree m + 1)|rows_j|)` and `uniformSpectrumBlockCount j |rows_j| ((j+1)|rows_j|)` are at most $|B_{\langle j, \mathrm{inr}\, i\rangle}|$.
--
--   Let $r =$ `preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s+1) Pmaster Plate` (a record of reals defined by OpenAI, with fields `Pbox`, `Vlog`, `Nlog`, `Q`, `baseAmbient`, `Dg`, `v`, `w`, `Banalytic`). Then for all reals $P_{\mathrm{proj}}, \mathrm{coarseTarget}, E_{\mathrm{coarse}}, p_{\mathrm{gain}}, \tau, P_{\mathrm{phys}}, \xi_n$ with $\xi_n > 0$ and $\xi_n \le$ `normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M_k Pphysical coarseTarget`; every finite set `cells` of `ColumnResiduePattern (Option Vars) (Fin nX) stride`; all vector polynomials $\mathrm{poly}_j$ on $\mathrm{Fin}\,n_X$ with values in $\mathbb R^{J_j}$, of degree at most $j+1$ (`DegreeLE 1 (j+1)`) and with coefficients in $U_j$ ($hmem$); and all reals $\mathrm{lossTarget}, P_{\mathrm{sample}}, R_{\mathrm{rank}}, S_{\mathrm{stride}}, \varepsilon_{\mathrm{sample}}, \eta_{\mathrm{sample}}$, assume, in order: $\mathrm{stride}_i > 0$; $N_i > 0$; $\tau > 0$; $0 \le P_{\mathrm{sample}}$; $n_X \le P_{\mathrm{sample}}$; $(s+2) n_X \le P_{\mathrm{sample}}$; $0 \le S_{\mathrm{stride}} \le e^{P_{\mathrm{sample}}}$; $\varepsilon_{\mathrm{sample}} > 0$; $1/\tau, 1/\varepsilon_{\mathrm{sample}} \le e^{P_{\mathrm{sample}}}$; $\mathrm{stride}_i \le S_{\mathrm{stride}}$; with $A_1$ the natural number chosen as witness of `exists_translated_physical_jet_l1_perturbation m (s+1)`, $\exp((P_{\mathrm{sample}} + A_1)^{A_1}) \le N_i$ for all $i$; `HasLayerSamplingRank (j+1) N Rrank (U j) (poly j)` for all $j$; $\exp((P_{\mathrm{sample}} + A_1)^{A_1}) \le R_{\mathrm{rank}}$; $\eta_{\mathrm{sample}} > 0$; $|$`CoefficientAmbientIndex (Fin (s+1)) J`$| \le P_{\mathrm{sample}}$; `affineAmbientPrimitiveBudget r.baseAmbient Qa` $\le P_{\mathrm{sample}}$, where $Q_a =$ `idealSiteLogBudget |Σ a, rows_{a.1}| (s+1) (r.Pbox + Prho + r.Vlog + r.Nlog + r.Q + target)`; $\sum_j |$`BoundedCoefficientExponent (Fin (s+1)) (j+1)`$| \le e^{P_{\mathrm{sample}}}$; $\eta_{\mathrm{sample}}^{-1} \le e^{P_{\mathrm{sample}}}$; $0 \le P_{\mathrm{phys}}$; $M_k \le e^{P_{\mathrm{phys}}}$; $m + 1 \le P_{\mathrm{phys}}$; $0 \le \mathrm{coarseTarget}$; $s + 2 \le P_{\mathrm{phys}}$; $|G| \le P_{\mathrm{phys}}$; $n_X \le P_{\mathrm{phys}}$; $\mathrm{lossTarget} +$ `coefficientErrorSpatialLog Pphysical` $+ 8 \le \mathrm{target}$; $\eta_{\mathrm{sample}}, \varepsilon_{\mathrm{sample}} \le e^{-\mathrm{target}}$.
--
--   With $A_{\mathrm{mass}}, A_{\mathrm{an}}, C_{\mathrm{grid}}$ the natural numbers chosen as witnesses of `exists_allocatedAffineModelMass_budget m (s+1)`, `exists_allocatedAffineAnalytic_budget m (s+1)` and `exists_preparedModularCanonicalDetector_grid_parameters m (s+1) canonicalTransitionLip`, put $F_{\mathrm{model}} = m 2^{s+1} (P_{\mathrm{master}} + 8)(1 + 4P_{\mathrm{master}}) + |\mathrm{LayerSamplerAxis}\ I\ n| \cdot m 2^{m+1} P_k + \sum_j |Q_j| \cdot |\mathrm{rows}_j| (m+1) P_k$, $Q_{\log} = (m+1) P_k + n_X Q_{\mathrm{stride}}$, $t_g = (s+1) + Q_{\log} + p_D + 2$, $p_g = C_{\mathrm{grid}} + (s+2) Q_{\log} + p_D + 5$ and $p = $ `slicedGridGeometryLog r.Dg r.v r.w t_g` $+ p_g$. Then for every real $P_{\mathrm{native}} \ge 0$, assume, in order: $r.\mathrm{Dg}, p, r.v, F_{\mathrm{model}}, P_\rho, P_k, \mathrm{target}, r.\mathrm{Banalytic}, P_{\mathrm{phys}}, E_{\mathrm{coarse}}, p_{\mathrm{gain}} \in [0, P_{\mathrm{native}}]$; $\mathrm{stride}_i \le e^{P_{\mathrm{phys}}}$; $1/\tau \le e^{P_{\mathrm{phys}}}$; $e^{-p_{\mathrm{gain}}}/2 \le g/2$; $p_{\mathrm{gain}} + 32$ is at most each of $P_{\mathrm{proj}}, \mathrm{coarseTarget}, E_{\mathrm{coarse}}, \mathrm{lossTarget}$. Then for every $C^{\mathrm{proj}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$, with $A_{\mathrm{cover}}, A_{\mathrm{sample}}$ the natural numbers chosen as witnesses of `exists_allocated_canonical_constructed_projection m (s+1)` and `exists_allocatedCanonicalProjection_composed_budget m (s+1) Acover`, $\mathrm{coverLog} = (P_{\mathrm{proj}} + s + 3 + A_{\mathrm{cover}})^{A_{\mathrm{cover}}}$ and $P_{\mathrm{mass}} = (P_{\mathrm{proj}} + A_{\mathrm{sample}})^{A_{\mathrm{sample}}}$, assume, in order: $\mathrm{coverLog} \le r.\mathrm{baseAmbient}$; $\mathrm{coverLog} \le P_{\mathrm{sample}}$; $P_{\mathrm{mass}} \le P_{\mathrm{sample}}$; $\|\phi_j(z)\| \le C^{\mathrm{proj}}_j \|z\|$; the covolume-ratio bounds above again; $n_X \le P_{\mathrm{mass}}$; $(s+2) n_X \le P_{\mathrm{mass}}$; $\mathrm{stride}_i \le e^{P_{\mathrm{mass}}}$; $1/\tau \le e^{P_{\mathrm{mass}}}$; with $A_w$ the witness of `exists_translated_physical_jet_density_window_mass m (s+1)`, $\exp((P_{\mathrm{mass}} + A_w)^{A_w}) \le N_i$ and $\le R_{\mathrm{rank}}$; $|$`CoefficientAmbientIndex (Fin (s+1)) J`$| \le P_{\mathrm{mass}}$; $\sum_j |$`BoundedCoefficientExponent (Fin (s+1)) (j+1)`$| \le e^{P_{\mathrm{mass}}}$; $|\mathrm{Vars}| \le e^{P_{\mathrm{phys}}}$; $1 \le P_{\mathrm{proj}}$; $m, |G| \le P_{\mathrm{proj}}$; $S.\mathrm{value} \le e^{P_{\mathrm{proj}}}$; $(m+1) P_k \le P_{\mathrm{proj}}$; $|\mathrm{Vars}| \le P_{\mathrm{proj}}$; $W \le e^{P_{\mathrm{proj}}}$ with $W =$ `allocatedPhysicalRootBudget B U basis S 0`; $R_j^{-1}, \sigma_j^{-1} \le e^{P_{\mathrm{proj}}}$; $|$`BoundedCoefficientExponent Vars (j+1)`$|, |I_j|, n_j, |J_j| \le P_{\mathrm{proj}}$; `probabilityProfileLipschitz` $\le e^{P_{\mathrm{proj}}}$; $C^{\mathrm{proj}}_j, V_{\mathrm{tail},j} \le e^{P_{\mathrm{proj}}}$; $n_X \le P_{\mathrm{proj}}$; $(|\mathrm{Vars}|+1) n_X \le P_{\mathrm{proj}}$; $\mathrm{stride}_i, \tau^{-1}, \xi_n^{-1} \le e^{P_{\mathrm{proj}}}$; with $A_{\mathrm{proj}}$ the second witness of `exists_allocated_canonical_constructed_projection m (s+1)`, $\exp((P_{\mathrm{proj}} + A_{\mathrm{proj}})^{A_{\mathrm{proj}}}) \le N_i$ and $\le R_{\mathrm{rank}}$. Then for every real $P_{\mathrm{side}}$ at least $P_{\mathrm{proj}}, P_{\mathrm{mass}}, P_{\mathrm{phys}}, \mathrm{coarseTarget}$, with $\exp((P_{\mathrm{side}} + A_c)^{A_c} + P_{\mathrm{proj}}) \le N_i$ for all $i$ ($A_c$ the witness of `exists_allocatedCanonicalSpatial_cutoff m`), and `cells` nonempty: let $\mathrm{bases} =$ `trimmedIntegerBox N (spatialTrimMargin τ N)` (assumed nonempty), $V =$ `narrowTrimmedSpatialWidths W τ ξn N`, assume $0 < \sum_z$ `selectedResidueSmoothWeight stride cells V z` and $0 <$ `selectedJointDensityMass bases stride cells V (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)`, let $\mathrm{pathLaw}$ be `allocatedOriginalPathLaw` (finite probability weights on $\mathrm{Path} = \mathrm{bases} \times$ `rectangularWeightIndices 0 V 1`), $\mathrm{sides} : \mathrm{Vars} \to \mathbb N$ be $S.\mathrm{value}$ on $G$ and `allocatedPrincipalSides B U basis S` on principal indices, $\mathrm{Sites} =$ `integerBox sides`, and $e : \mathrm{Sites} \to (\mathrm{Vars} \to \mathbb Z)$ the inclusion.
--
--   For all families, indexed by $z \in \mathrm{Path}$ and nonempty types $\mathrm{Tests}_z$, of rational Lie algebras $L_{z,j}$ with Hausdorff vector topologies on $\mathbb R \otimes_{\mathbb Q} L_{z,j}$, `RationalFilteredNilmanifold` $D_{z,j}$ of degree $s$, niltests $V_{z,j}$ on $D_{z,j}$ (constant weight $1$), finite sets $\mathrm{slices}_{z,j} \subseteq \mathrm{Sites}$, centers $c_{z,j} : \mathrm{Vars} \to \mathbb Z$, steps $\mathrm{step}_{z,j}$ and heights $H_{z,j} : \mathrm{Vars} \to \mathbb N$: assume $\mathrm{step}_{z,j} > 0$; $e(\mathrm{slices}_{z,j}) =$ `commonStrideBox c step H` (the product of the progressions $c_i + \mathrm{step}\cdot k$, $0 \le k < H_i$); `IsDenseCommonStrideBox sides pSlice` $e(\mathrm{slices}_{z,j})$; $|\mathrm{Vars}| \le P_{\mathrm{detect}}(q_D)$; each $V_{z,j}$ has complexity at most $P_{\mathrm{detect}}(q_D)$ and norm bound at most $1$; $(s+1)(s+3) \le |G|$; $M_k \le S.\mathrm{value}$. With $C_b, A_n, A_{\mathrm{nat}}, A$ the witnesses of `exists_canonicalSlicedNative_input_budget m (s+1) Amass Aan`, `exists_allocatedRecenteredFactor_normalization m (s+1)`, `exists_native_partner_of_physical_cube_mixture_all_degrees s` and `exists_normalizedNative_uniform_budget m A_n A_nat`, put $\mathrm{budget} = ((P_{\mathrm{native}} + C_b)^{C_b} + A)^A$. Assume finally $0 \le u$, $0 \le p_{\mathrm{model}}$, $p_{\mathrm{slice}} \le p_{\mathrm{model}}$, $|\mathrm{Vars}| \le e^{p_{\mathrm{model}}}$, $e^{-(2u + 4p_{\mathrm{model}} + 7)} \le \alpha \le 1$, and let $\mathrm{signal} : (\mathrm{Fin}\,n_X \to \mathbb Z) \to \mathbb C$ have $\|\mathrm{signal}\| \le 1$, vanish outside `integerBox N`, and satisfy $\alpha \le$ `sampledSliceSeminorm pathLaw F slices w signal`, where $F(z, t) =$ `jointIntegerPhysicalSite (e t) (z₁, z₂)` and $w(z, j, t) = \overline{V_{z,j}(\mathrm{commonStrideIndex}(c_{z,j}, \mathrm{step}_{z,j}, e(t)))}$.
--
--   **Conclusion.** There exist a `NormalizedPolynomialTwist (Fin nX) (Σ j, J j) e^budget e^budget e^budget` $\mathrm{tw}$ (a structure bundling a modulus and cover number at most $e^{\mathrm{budget}}$, a mask of norm at most $1$ and an $e^{\mathrm{budget}}$-Lipschitz smooth function of norm at most $1$) and $F_{\mathrm{native}} :$ `integerBox N` $\to \mathbb C$ such that there is a `NativeSampleModel 1 s budget (t ↦ t) Fnative` (a nilmanifold of degree $s$ with a niltest of norm bound at most $1$ and complexity at most $\mathrm{budget}$ whose values give $F_{\mathrm{native}}$) and
--   $$e^{-\mathrm{budget}} \le \Bigl\| \mathop{\mathbb E}_{t \in \mathrm{integerBox}\,N} \mathrm{signal}(t)\, \overline{\overline{\mathrm{tw.eval}(N, \mathrm{poly}, t)}\, F_{\mathrm{native}}(t)} \Bigr\|$$
--   (the `correlation` under the uniform weights on `integerBox N`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDirectDetectionAmbient_sharedWidth` (in `lean/OAI/Combinatorics/Progressions/Estimates/SharedWidthPreparedModularGeneralDirectDetectionFreeTrim.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B277` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/SharedWidthPreparedModularGeneralDirectDetectionFreeTrim.lean (declaration OAI.Erdos3.VectorPolynomial.preparedModularGeneralDirectDetectionAmbient_sharedWidth)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
variable (α : ℝ)
variable {P : ℝ}

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

include hb o bW μ ν μrows hR hσ in

theorem preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2 (hsm : s ≤ m)
    (Pchart D target Pk Prho Qstride : ℝ) (K : ℝ≥0)
    (geometry : AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K)
    {Pmaster Plate : ℝ} (hLate : Pmaster ≤ Plate) (hMaster : 0 ≤ Pmaster) (hDMaster : D ≤ Pmaster)
    (hPkMaster : Pk ∈ Set.Icc 0 Pmaster) (hQstrideMaster : Qstride ∈ Set.Icc 0 Pmaster)
    (hDetectMaster : pDetect ∈ Set.Icc 0 Pmaster) (hnXMaster : (nX : ℝ) ≤ Pmaster)
    (hRone : ∀ j, R j ≤ 1)
    (hRiMaster : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hKMaster : (K : ℝ) ≤ Real.exp Pmaster)
    (hcutoffMaster : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pmaster)
    (hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
    (hMkPk : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (hstride : ∀ i, 0 < stride i) (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForwardMaster : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pmaster)
    (hVtailMaster : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pmaster)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩)) :
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let Pbox := r.Pbox
    let Vlog := r.Vlog
    let Nlog := r.Nlog
    let Mlog := r.Q
    let baseAmbient := r.baseAmbient
    let _Qgrid := Real.toNNReal (8 * (D + 1))
    let Ag := canonicalTransitionLip
    let Dg := r.Dg
    let vg := r.v
    let wg := r.w
    let Banalytic := r.Banalytic
    let Pnum := Pmaster
    ∀ {Pproj coarseTarget Ecoarse pGain : ℝ},
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {τ Pphysical : ℝ},
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn),
    ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
,
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
    (_hPhysicalNonneg : 0 ≤ Pphysical) → (_hMkPhysicalBound : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pphysical) →
    (_hmPhysicalBound : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) → (_hCoarseNonneg : 0 ≤ coarseTarget) →
    (_hDimPhysicalBound : (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical) →
    (_hGPhysicalBound : (Fintype.card G : ℝ) ≤ Pphysical) →
    (_hXPhysicalBound : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical) →
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
    ∀ (Cproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1))
    let coverLog := (Pproj + ((s + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (s + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j) →
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
    (∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) → (∀ j, (Vtail j : ℝ) ≤ Real.exp Pproj) →
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
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    ∀ (hbases : bases.Nonempty),
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    (htotal : 0 < selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)) →
    let Path := bases × rectangularWeightIndices 0 V 1
    let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N
      (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW hτSpatial hξn stride cells hmass bases hbases htotal
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    (s + 1) * (s + 3) ≤ Fintype.card G → (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) ≤ S.value →
    let Cbudget := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + Cbudget) ^ Cbudget
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{0,0,0,0,0,0} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    0 ≤ u → 0 ≤ pModel → pSlice ≤ pModel →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp pModel →
    Real.exp (-(2 * u + 4 * pModel + 7)) ≤ α → α ≤ 1 →
    ∀ (signal : (Fin nX → ℤ) → ℂ),
    (∀ t, ‖signal t‖ ≤ 1) → (∀ t, t ∉ integerBox N → signal t = 0) →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun t : integerBox N => t.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun t => signal t.val) (fun t => star (twistData.eval N poly t.val) * Fnative t)‖ := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
