-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_relativePatchSliceConclusion_of_normalized_ready_s2
-- name    : OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_normalized_ready_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:04:37.235179+00:00
-- url     : https://prove2.me/theorems/c6d334a9-b64b-4680-98a2-49352c2f7ad8
-- title:
--   A ready normalized allocated candidate conclusion, with all forecast and budget hypotheses, yields a relative patch slice conclusion at density (1 - ε)λ
-- statement:
--   This statement lives in a large context of data and structures defined by OpenAI; we follow the Lean `variable` declarations. Fix a natural number $m$, finite types $G$, $X$ and a type $J_0$; a rank preparation family `prep : RankPreparationFamily X J₀ m` (for each $j < m$ a real subspace `(prep j).space` of $\mathbb{R}^{(\texttt{prep } j).\mathrm{Coord}}$, a polynomial `(prep j).poly`, a rank `(prep j).rank`, and prepared coordinates) with prepared heights `hprep : prep.PreparedHeights preparationP Rprep`, where $0 \le \mathrm{preparationP}$ and $1 \le \mathrm{Rprep}$; finite types $I_j$, $E^{\mathrm{out}}_j$, natural numbers $n_j$, finite types $B_a$ for the layer sampler axes $a$; bases $b_j$ of the orthogonal complements of the Euclidean subspaces of `(prep j).space` whose $\mathbb{Z}$-span is the projected integer lattice; reals $R_j, \sigma_j > 0$; a layer sampler scale $S$ (main field `S.value`); natural numbers $D_{\mathrm{mod}}, L_{\mathrm{rank}}$ and embeddings `spatial`, `kernel`, `block`; an embedding $e_{\mathrm{Spatial}} : \{0,1\} \times X \hookrightarrow G$; $N : X \to \mathbb{N}$ and reals $\tau, \xi, \mathrm{cost}$; an `ActualFixedSpatialForecastSetup` $s$ (with numerical fields including $s.D$, $s.P$, $s.P_{\mathrm{bad}}$, $s.P_{\mathrm{pres}}$, $s.P_\tau$, $s.\kappa$); two sliced forecast numerics $q_{\mathrm{num}}, q_{\mathrm{Late}}$ for $s$ (OpenAI's `ActualFixedSpatialSlicedForecastNumerics s`, with fields including `Hchild`, `δ`, `v`, `Ptail`, `capLog`, `E`, `Pnative`, `massLog`); orthonormal bases $o_j$; $\mathbb{Z}$-bases $bW_j$ of the lattice sections (each lattice section assumed to be a $\mathbb{Z}$-lattice); left-invariant probability measures $\nu_j$ on the corresponding tori, whose product is assumed compact; strides $X \to \mathbb{N}$, a finite set of column residue cells, a center on the coefficient torus; and an `AllocatedExternalCandidateSampler` $A$ (with sites, paths, a law `A.law`, sides `A.sides k` and widths `A.widths`). Let $V$ denote the number of layer sampler variables, let $\beta$ be the natural number chosen by OpenAI from the lemma `exists_relative_finite_returned_fiber_normalization` at `degree`, $\gamma$ = `allocatedNormalizedShearObservableExponent degree` (also chosen by OpenAI from an existence lemma), and $Z = ((\mathrm{childCost} + V + 2) + 2)^{\beta}$.
--
--   Further fix natural numbers $\mathrm{degree}$, $\mathrm{originalRank}$, $D$, $E$, $\mathrm{netExponent}$, a function $f : \mathbb{Z}^{X} \to \mathbb{R}$, reals $\lambda$, chartCost, childCost, gainLog, gain, $p_{\mathrm{Global}}$, and a finite set `productive` of paths of $A$, and assume the following context hypotheses: $0 \le \mathrm{childCost}$; $e^{-\mathrm{gainLog}} \le \mathrm{gain}$; $\mathrm{gain}/16 <$ (mass of `productive` under `A.law`); $(Z + 2)^{\gamma} \le p_{\mathrm{Global}}$; $0 \le p_{\mathrm{Global}}$; $\mathrm{chartCost} \le p_{\mathrm{Global}}$; $Z \le p_{\mathrm{Global}}$; $\mathrm{gainLog} + 16 + (\mathrm{degree} + 1)\,\mathrm{childCost} + Z \le p_{\mathrm{Global}}$; $f(x) \in [0,1]$ for all $x$; $\lambda \in [0,1]$; `A.DegreeGlobalizationAt (fun x => f x - λ) degree netExponent p_Global cost` (an OpenAI proposition); $G$ is nonempty; $q_{\mathrm{num}}.\mathrm{Hchild} \le \texttt{S.value}$; $2 \le e^{-\mathrm{cost}}\cdot\texttt{S.value}$; $q_{\mathrm{num}}.\delta \le e^{-\mathrm{cost}}$; $\mathrm{cost} + 1 \le q_{\mathrm{num}}.v$; $\mathrm{cost} + 1 \le s.P_{\mathrm{pres}}$; $2e^{\mathrm{cost}} \le q_{\mathrm{num}}.\mathrm{Ptail}$.
--
--   The theorem then takes the following arguments and hypotheses.
--   - $\mathrm{centerLift}_j \in$ `(prep j).space` and $H_{\mathrm{initial}} \in \mathbb{N}$ with $H_{\mathrm{initial}} = q_{\mathrm{num}}.\mathrm{Hchild}$; and `AllocatedNormalizedCandidateConclusion degree (fun k => H_initial ≤ A.sides k) centerLift productive childCost chartCost (originalRank + degree·E) f λ` (an OpenAI proposition).
--   - $q_{\mathrm{num}}$ and $q_{\mathrm{Late}}$ have equal fields $\delta$, Hchild, $v$ and Ptail.
--   - $\xi \le 1$, and $2\lceil \tau N_x/4 \rceil \le N_x$ for every $x$ (OpenAI's `spatialTrimMargin`).
--   - Reals $u, p, p_{\mathrm{Slice}}, p_{\mathrm{Test}}, \mathrm{localBudget}, \mathrm{precision}, C, E_{\mathrm{compare}}, P_{\mathrm{test}}, R_{\mathrm{rank}}, C_{\mathrm{recovered}}$ with: $0 \le u$, $0 \le p$, $0 \le \mathrm{localBudget}$, $p_{\mathrm{Slice}}\,V \le p$, $1 \le C \le e^{p}$, $q_{\mathrm{num}}.\mathrm{capLog} \le p$, $2u + 4p + 12 \le q_{\mathrm{num}}.E$, and `actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p` $\le \mathrm{precision}$.
--   - `A.NativeDetection 0 p_Slice p_Test localBudget (forecastAugmentedUnitThreshold u p (exp(p_Slice·V)) C (exp qnum.capLog))` (OpenAI propositions and quantities).
--   - The excess mass $\sum_{w} \max\bigl(\pi(w) - C\,\mathrm{unif}(w), 0\bigr)$ of the site law $\pi$ of `A.law` on OpenAI's physical box, relative to the uniform distribution on the integer box $\prod_x \{0,\dots,N_x - 1\}$, is at most $6\,e^{-(2\,\mathrm{precision} + 4)}$.
--   - $0 \le p_{\mathrm{Slice}}$, $\mathrm{cost} \le p_{\mathrm{Slice}}$, $\mathrm{chartCost} \le p_{\mathrm{Slice}}$, $2 \le p_{\mathrm{Test}}$, and $\sigma_j \le 1$ for all $j$.
--   - A bijection $e$ from $\{0, \dots, \mathrm{tagCount}-1\}$ to the prepared coordinates of `prep`.
--   - $2\,\mathrm{cost} + 6 \le u$; $\max\bigl(\max(\mathrm{localBudget}, 3q_{\mathrm{num}}.\mathrm{Pnative} + 3),\ 2u + 4p + \max(0, q_{\mathrm{num}}.\mathrm{massLog}) + 20\bigr) + 2 + 2\,\mathrm{cost} + 8 \le E_{\mathrm{compare}}$; $\max(\mathrm{localBudget}, 3q_{\mathrm{num}}.\mathrm{Pnative} + 3) \le P_{\mathrm{test}}$.
--   - With $\Sigma$ = `s.slicedComparisonSourceLog P_test` (OpenAI): $|\sigma_j| \le \exp\bigl(-\texttt{fixedPathSlicedPerturbationLog}\ s.D\ (s.D + \Sigma + 4)\ (\mathrm{cost} + 1)\ (2\Sigma + (E_{\mathrm{compare}} + 4) + 14)\ m\bigr)$ for all $j$.
--   - $s.\kappa$ equals `forecastGeometricJacobian` of the subspaces, $b$, $R$, `S.value`, the product of the basis axis scales $\lceil 1/\lVert b_j(i) \rVert\rceil$ over the short integer selection, and $\tau$ (OpenAI).
--   - $0 \le q_{\mathrm{Late}}.\mathrm{massLog} + E_{\mathrm{compare}} + 8$; and with $\Theta = \exp\bigl((\max(\max(s.P, 2\max(P_{\mathrm{test}}, 3q_{\mathrm{Late}}.\mathrm{Pnative} + 3) + 1), q_{\mathrm{Late}}.\mathrm{massLog} + E_{\mathrm{compare}} + 8) + \epsilon_m)^{\epsilon_m}\bigr)$, where $\epsilon_m$ = `nativeForecastAmbientExponent m`: $\Theta \le N_i$ for all $i$, and $\Theta \le R_{\mathrm{rank}}$.
--   - `HasLayerSamplingRank (j+1) N R_rank (prep j).space (prep j).poly` for every $j$ (OpenAI).
--   - Functions `sampleFn` (to OpenAI's coefficient sampler arrays) and `readFn` (to integer coefficient arrays), of a base point and an integer assignment, such that `AllocatedCenteredRecoveredSampleReadAt … C_recovered center centerLift base (sampleFn base) (readFn base)` holds for every base, and `AllocatedCenteredFramedRecoveredSampleAt …` holds at every productive path $z$ (OpenAI propositions).
--   - For every productive path $z$: with the primes $\mathcal{P}$ up to $\lceil e^{2P_{\mathrm{test}}}\rceil$, the product over $p \in \mathcal{P}$ of $p$ raised to OpenAI's `largestTestedBadDepth` (with exponents $\lfloor\log_p \lceil e^{2P_{\mathrm{test}}}\rceil\rfloor$ and the bad predicate `allocatedActualPrimeBad … (modularForecastRankConstant m D_mod)`) of the jointly framed read of $z$ is at most $(\prod_x \mathrm{stride}_x)^2 \cdot$ `smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)` $\cdot$ `quantitativeBadPrimeRadius (gainLog + 8)`.
--   - For every productive path $z$ and $t \in \{0,1\}$: `spatialMatrixBlockThreshold |X| (jointSpatialError gainLog)`$/2 < |\det M_{z,t}|$, where $M_{z,t}$ is the $X \times X$ matrix of OpenAI's `spatialMatrixNormalizedEntries eSpatial A.widths` at $z$ and $t$.
--   - Reals $P_{\mathrm{dim}}, Q_{\mathrm{stride}}$ with $0 \le P_{\mathrm{dim}}$, $|X| \le P_{\mathrm{dim}}$, $V \le P_{\mathrm{dim}}$, $0 < |X|$, $0 \le \mathrm{gainLog} \le P_{\mathrm{dim}}$, $\mathrm{stride}_x \le e^{Q_{\mathrm{stride}}}$ for all $x$, `preparedCenteredForecastSpatialLog P_dim` $\le s.P$, and $2|X|Q_{\mathrm{stride}} +$ `smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)` $+ \mathrm{gainLog} + 11 \le s.P_{\mathrm{bad}}$.
--   - $0 \le \mathrm{cost}$, $0 \le E_{\mathrm{compare}}$, $\tau \le 1$; `comparisonPrecisionFloor s (D_mod + Σ_j |I_j|) Σ (2 P_test) E_compare` $\le \texttt{S.value}$; $\xi \le \exp(-(2\Sigma + (E_{\mathrm{compare}} + 4) + 14))$; $E_{\mathrm{compare}} + 8 \le q_{\mathrm{Late}}.E$; and $\exp\bigl(\texttt{forecastJointGridAmbientLog}\ (D_{\mathrm{mod}} + \textstyle\sum_j |I_j|)\ (\texttt{comparisonGridLog}\ s\ \Sigma)\ (E_{\mathrm{compare}} + 4)\ (2P_{\mathrm{test}})\ s.P_\tau\bigr) \le N_i$ for all $i$ (OpenAI quantities).
--   - $|(\texttt{prep } j).\mathrm{Coord}| \le \mathrm{preparationP}$ for all $j$, and $\lVert bW_j(a) \rVert \le \exp\bigl((\mathrm{preparationP} + 2)^{\texttt{preparedIntegralBasisExponent}\ m}\bigr)$ for all $j, a$.
--   - Reals $\varepsilon, \mathrm{crtBudget}$ with $0 < \varepsilon \le 1$, $1 \le \mathrm{crtBudget}$, $\varepsilon^{-1} \le \mathrm{crtBudget}$, and $P_{\mathrm{test}}, s.P_{\mathrm{bad}}, s.P_{\mathrm{pres}} \in [0, \mathrm{crtBudget}]$.
--   - $m \le \mathrm{degree}$ and $\sum_j (\texttt{prep } j).\mathrm{rank} \le m D$.
--   - A real $\mathrm{budget}$ with $1 \le \mathrm{budget}$, $\mathrm{childCost} + \mathrm{degree}\cdot D \le \mathrm{budget}$, $D_{\mathrm{mod}} \le \mathrm{budget}$, $2048\,\mathrm{crtBudget}^3 + (\mathrm{preparationP} + 2)^{\texttt{preparedIntegralBasisExponent}\ m + 1} \le \mathrm{budget}$, $2Z + 1 \le \mathrm{budget}$, $q_{\mathrm{num}}.\mathrm{capLog} \le \mathrm{budget}$, $q_{\mathrm{num}}.\mathrm{Pnative} \le \mathrm{budget}$, $\mathrm{cost} \le \mathrm{budget}$, and $\exp(\Xi) \le N_i$ for all $i$, where $\Xi$ = `spatialPatchExtractionCost (recoveredKernelScalarBudget budget)` $= 20\,(8(\mathrm{budget} + 1)^2 + 1)^2$.
--
--   Conclusion: `RelativePatchSliceConclusion degree N f ((1 - ε)λ) (originalRank + degree·(D + E)) Ξ` holds. By OpenAI's definition this says: there exist a natural number $q > 0$, a residue slice $S'$ of the box $\prod_x\{0,\dots,N_x-1\}$ with modulus $q$ (starts $b_x$ and lengths $\ell_x$ with $b_x + qk < N_x$ for $k < \ell_x$), a natural number $d$ and a polynomial patch $P$ (an OpenAI `PolynomialPatch X degree d`, with value in $[0,1]$) such that $e^{-\Xi} N_x \le \ell_x$ for all $x$, $d \le \mathrm{originalRank} + \mathrm{degree}\,(D + E)$, $d + \log(1 + \operatorname{lip}(P)) \le \Xi$, and $e^{-\Xi} \le \mathbb{E}_{k}\,\bigl(f(b + qk) - (1-\varepsilon)\lambda\bigr)\,P.\mathrm{value}(k)$, the average over $k \in \prod_x \{0,\dots,\ell_x - 1\}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_normalized_ready_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_normalized_ready` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedSourceGeometryNormalizedPatchConclusion.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B304`, `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedSourceGeometryNormalizedPatchConclusion.lean (declaration OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_normalized_ready)

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

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable (eSpatial : Fin 2 × X ↪ G)
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

local instance instNonemptySiteCoord_r80f68a_1 : Nonempty A.Site := A.site_nonempty
variable {degree originalRank D E : ℕ}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost childCost : ℝ} {productive : Finset A.Path}
variable {gainLog gain pGlobal : ℝ} {netExponent : ℕ}
variable (hchild : 0 ≤ childCost)
  (hgain : Real.exp (-gainLog) ≤ gain)
  (hReady : gain / 16 < A.law.mass productive)
  (hregularityBudget : ((((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 2) ^
    allocatedNormalizedShearObservableExponent degree ≤ pGlobal)
  (hpGlobal : 0 ≤ pGlobal) (hchartGlobal : chartCost ≤ pGlobal)
  (hscoreGlobal : (((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hmassGlobal : gainLog + 16 + ((degree : ℝ) + 1) * childCost + (((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hfGlobal : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
  (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
  (rule : A.DegreeGlobalizationAt (E := Eout) (fun x => ((f x - lam : ℝ) : ℂ))
    degree netExponent pGlobal cost)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

include ν hpPrep hRprep hchild hgain hReady
  hregularityBudget hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule
  hkernel hcutoff hlate hdensity hlog hprescribed hstride in

theorem relativePatchSliceConclusion_of_normalized_ready_s2

    (centerLift : ∀ j, (prep j).space) (Hinitial : ℕ)
    (hInitialCutoff : Hinitial = qnum.Hchild)
    (hinit : AllocatedNormalizedCandidateConclusion (E := Eout) (A := A)
      degree (fun k => Hinitial ≤ A.sides k) centerLift productive childCost chartCost
      (originalRank + degree * E) f lam)
    (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
    (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : qnum.capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ qnum.E)
    (hPrecision : actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp qnum.capLog)))
    (hexcess : letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    (hσ1 : ∀ j, σ j ≤ 1)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    (hU : cost + cost + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * qnum.Pnative + 3))
        (2 * u + 4 * p + max 0 qnum.massLog + 20) + 2 +
      cost + cost + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * qnum.Pnative + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      s.D (s.D + s.slicedComparisonSourceLog Ptest + 4) (cost + 1)
      (2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14) m))
    (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) (fun j : Fin m => (prep j).space) b R S.value
      (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).1)
        ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).2 : ℝ)) τ)
    (hEprec : 0 ≤ qLate.massLog + Ecompare + 8)
    (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ base, AllocatedCenteredRecoveredSampleReadAt B (fun j : Fin m => (prep j).space)
      bW b hb o S hR hσ (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value)
      spatial kernel block Crecovered center centerLift base (sampleFn base) (readFn base))
    (hrecovered : ∀ z ∈ productive, AllocatedCenteredFramedRecoveredSampleAt
      B (fun j : Fin m => (prep j).space) b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      centerLift z.1.val z.2.val (sampleFn z.1.val z.2.val)
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val)))
    (hgood : let primes := boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊
      letI := actualForecastPrimeNeZero primes (boundedPrimes_prime _)
      ∀ z ∈ productive,
      (∏ p ∈ primes, p ^ largestTestedBadDepth (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val))) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hdet : ∀ z ∈ productive, ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries eSpatial A.widths z.2.val (t,j,i))|)
    {Pdim Qstride : ℝ}
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstrideSource : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ s.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ s.Pbad)
    (hcost : 0 ≤ cost) (hE : 0 ≤ Ecompare) (hτ1 : τ ≤ 1)
    (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) Ecompare ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14)))
    (hEdata : Ecompare + 8 ≤ qLate.E)
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ))
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    {ε crtBudget : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hCRTbudget : 1 ≤ crtBudget) (hCRTinv : ε⁻¹ ≤ crtBudget)
    (hCRTtest : Ptest ∈ Set.Icc 0 crtBudget)
    (hCRTbad : s.Pbad ∈ Set.Icc 0 crtBudget)
    (hCRTpres : s.Ppres ∈ Set.Icc 0 crtBudget)
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * D)
    {budget : ℝ}
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : childCost + (degree : ℝ) * D ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : 2048 * crtBudget ^ 3 + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : 2 * (((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
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
