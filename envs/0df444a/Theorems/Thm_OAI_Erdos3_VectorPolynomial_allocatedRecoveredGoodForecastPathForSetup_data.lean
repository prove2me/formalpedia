-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRecoveredGoodForecastPathForSetup_data
-- name    : OAI.Erdos3.VectorPolynomial.allocatedRecoveredGoodForecastPathForSetup_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:38:39.404724+00:00
-- url     : https://prove2.me/theorems/8ffbe27b-927c-4b6c-9da9-58330743e19f
-- title:
--   The recovered good forecast path for a setup has the prescribed fields
-- statement:
--   Let $m$ be a natural number; $G, X$ finite types with decidable equality on $X$; $I_j, E_j, J_j$ ($j \in \mathrm{Fin}\,m$) finite types; $n : \mathrm{Fin}\,m \to \mathbb N$; $B_a$ finite types for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); $U_j \le \mathbb R^{J_j}$ real subspaces; $b_j$ bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, with $\mathbb Z$-span `projectedIntegerLattice (euclideanSubspace (U j))` (hypothesis $hb$); $R, \sigma : \mathrm{Fin}\,m \to \mathbb R$ with $R_j, \sigma_j > 0$ (hypotheses $hR$, $h\sigma$) and $S$ a `LayerSamplerScale` for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); $o_j$ orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; $N : X \to \mathbb N$; vector polynomials $\mathrm{poly}_j$ on $X$ with values in $\mathbb R^{J_j}$ whose coefficients all lie in $U_j$ (hypothesis $hm$); reals $\tau, \xi$; $\mathrm{stride} : X \to \mathbb N$; a finite set `cells` of `ColumnResiduePattern (Option Vars) X stride` (functions assigning to each $(k, x)$ a residue mod $\mathrm{stride}(x)$), where $\mathrm{Vars} =$ `LayerSamplerVariables G I n B`; a point `center` of the `CoefficientTorus U`; and a proof $A$ of `AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center` (a proposition bundling positivity of $N$, $\tau$, $\xi$, the strides and certain masses).
--
--   Let $z$ be a point of `A.Path`, i.e. a pair of a point $z_1$ of `trimmedIntegerBox N (spatialTrimMargin τ N)` and a point $z_2$ of `rectangularWeightIndices 0 (allocatedExternalCandidateWidths B U b S N τ ξ) 1`; let $\mathrm{centerLift}_j \in U_j$; let `sample : CoefficientSamplerArrays I n` and $f :$ `AllocatedActualCoefficientIndex G X I E n B` $\to \mathbb Z$ satisfy `AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm centerLift z₁ z₂ sample f` (hypothesis `hrecovered`). Let $D_{\mathrm{mod}}$ and $L$ be natural numbers, with embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j` with $\mathrm{short} =$ `allocatedShortAxis U b S.value`), and $e : \mathrm{Fin}\,2 \times X \hookrightarrow G$. Let $P_{\mathrm{dim}}, \mathrm{gainLog}, Q_{\mathrm{stride}}$ be reals, `primes` a finite set of primes (hypothesis `hprime`) and $\mathrm{depth} : \mathbb N \to \mathbb N$, with: (`hgood`) $\prod_{p \in \mathrm{primes}} p^{\mathrm{largestTestedBadDepth}(\mathrm{depth}, \mathrm{bad}, p, f)} \le \bigl(\prod_x \mathrm{stride}(x)\bigr)^2 \cdot \mathrm{smallPrimePowerCorrection}(\mathrm{modularCoefficientPrimeThreshold}\ m) \cdot \mathrm{quantitativeBadPrimeRadius}(\mathrm{gainLog} + 8)$, where $\mathrm{bad}$ is `allocatedActualPrimeBad short spatial kernel block primes (modularForecastRankConstant m Dmod)` and `largestTestedBadDepth A bad p x` is the largest $a \in [1, A(p)]$ with $\mathrm{bad}\ p\ a\ x$ (or $0$); $0 \le P_{\mathrm{dim}}$; $|X| \le P_{\mathrm{dim}}$; $|\mathrm{Vars}| \le P_{\mathrm{dim}}$; $|X| > 0$; $0 \le \mathrm{gainLog} \le P_{\mathrm{dim}}$; $\mathrm{stride}(x) \le e^{Q_{\mathrm{stride}}}$ for all $x$; and (`hdet`) for each $t \in \mathrm{Fin}\,2$, `spatialMatrixBlockThreshold |X| (jointSpatialError gainLog)` $/2$ is less than the absolute value of the determinant of the $X \times X$ matrix with entries `spatialMatrixNormalizedEntries e A.widths z₂ (t, j, i)`. Finally let `Selected` be a type, $\mathrm{selected} : \mathrm{Selected} \to \Sigma_j\, \mathrm{Fin}(n_j)$, $\delta_{\mathrm{slice}}$ real, `setup` an `ActualFixedSpatialForecastSetup B U b S Dmod selected τ δslice` (over $X$ and $E$; a structure bundling inequalities and real parameters including `setup.P` and `setup.Pbad`), with `preparedCenteredForecastSpatialLog Pdim` $\le$ `setup.P` and $2|X| Q_{\mathrm{stride}} + \mathrm{smallPrimePowerCorrection}(\mathrm{modularCoefficientPrimeThreshold}\ m) + \mathrm{gainLog} + 11 \le$ `setup.Pbad`.
--
--   Let `path` be `allocatedRecoveredGoodForecastPathForSetup` applied to all of these data and proofs (an `ActualFixedSpatialForecastPath` defined by OpenAI). Then `path.center` $= \mathrm{centerLift}$, `path.base` $= z_1$, `path.noise` $= z_2$, `path.sample` $=$ `sample`, `path.read` $=$ `allocatedReplaceReadNoise B z₂ f` (the read-off equal to $z_2$ on the noise indices and to $f$ on the other indices), `path.primes` $=$ `primes`, `path.exponent` $= \mathrm{depth}$, `path.prescribed` is identically $0$, `path.origin` is identically $0$, `path.lower` is identically $0$, and `path.width` is identically $1$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedRecoveredGoodForecastPathForSetup_data` in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedRetainedActualForecastFactory.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1331` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedRetainedActualForecastFactory.lean#L106

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1331

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j ex, coefficients (poly j) ex ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

variable (z : A.Path) (centerLift : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      centerLift z.1.val z.2.val sample f)
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (Pdim gainLog Qstride : ℝ)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime) (depth : ℕ → ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth depth
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) U b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hdet : ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries e A.widths z.2.val (t,j,i))|)

variable {Selected : Type}
    {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ setup.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ setup.Pbad)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedRecoveredGoodForecastPathForSetup_data :
    let path := allocatedRecoveredGoodForecastPathForSetup z centerLift sample f hrecovered Dmod spatial kernel block e Pdim gainLog Qstride
      primes hprime depth hgood hPdim hX hvars hnX hgainLog hgainDim hstride hdet
      setup hPmodel hPbad
    path.center = centerLift ∧ path.base = z.1.val ∧ path.noise = z.2.val ∧
      path.sample = sample ∧ path.read = allocatedReplaceReadNoise B z.2.val f ∧
      path.primes = primes ∧ path.exponent = depth ∧ path.prescribed = (fun _ => 0) ∧
      path.origin = (fun _ _ => 0) ∧ path.lower = (fun _ _ => 0) ∧ path.width = (fun _ _ => 1) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
