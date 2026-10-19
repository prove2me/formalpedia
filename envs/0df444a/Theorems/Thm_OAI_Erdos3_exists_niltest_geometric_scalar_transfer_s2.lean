-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_niltest_geometric_scalar_transfer_s2
-- name    : OAI.Erdos3.exists_niltest_geometric_scalar_transfer_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:50:43.998562+00:00
-- url     : https://prove2.me/theorems/f8246baa-64fc-4d8f-8f6f-6c712776c391
-- title:
--   Geometric scalar transfer of a niltest upper comparison to smooth affine samples
-- statement:
--   For every natural number $s$ there is a natural number $E \ge 2$ such that the following holds.
--
--   **Data.** Let $\iota$ be a finite linearly ordered type, $I$ and $J$ finite types, and $V$ a Lie algebra over $\mathbb{Q}$ with the topological-vector-space instances (topological additive group, continuous scalar multiplication, Hausdorff) on $\mathbb{R} \otimes_{\mathbb{Q}} V$ (with $\iota$, $I$, $V$ in arbitrary universes $w$, $u$, $v$); let $d$ be a natural number and `nilmanifold` a `RationalFilteredNilmanifold V s d` (OpenAI: a rational filtered nilmanifold of step $s$ and dimension $d$). Let $p, \varepsilon, Z, U, \mathrm{gridLog}, \mathrm{ratioLog}, \mathrm{meshLog}, \mathrm{level}, \mathrm{budget}$ be reals with: $2 \le p$; $0 < \varepsilon \le 1$; $0 \le Z$, $0 \le U$, $0 \le \mathrm{meshLog}$; $p \le U$, `scalarTransferTail (3p)` $\le U$, $Z \le U$, $\mathrm{gridLog} + \mathrm{ratioLog} + 2 \le U$, $\varepsilon^{-1} \le e^U$; $e^{-p} \le \mathrm{level} \le 2$; $\lvert I\rvert \le U$, $\lvert \texttt{Option}\ J \times I\rvert \le U$, $\lvert J\rvert \le U$ and $\lvert J\rvert \ge 2$. Let $g$ be a niltest on `nilmanifold` in the variables $I$ (all weights $1$) with complexity at most $p$ (`g.ComplexityLE p`). Let $\mathrm{prime}, \mathrm{power} : \iota \to \mathbb{N}$ with every $\mathrm{prime}(i)^{\mathrm{power}(i)} \ne 0$, every $\mathrm{prime}(i)$ prime, $\mathrm{prime}$ injective, $\lvert\iota\rvert \le e^Z$ and $\mathrm{prime}(i)^{\mathrm{power}(i)} \le e^Z$. Let $D$ be a natural number with $0 < D \le e^Z$ and $\mathrm{anchor} : J \to \mathbb{Z}$.
--
--   **Derived quantities.** $p_{\mathrm{ref}}$ = `affineReferenceInput ε U`, $\mathrm{common}$ = `affineCommonReferenceBudget E ε U`, $A_{\mathrm{ref}} = \lceil (p_{\mathrm{ref}} + 2)^E\rceil$ (natural-number ceiling), $b$ = `adaptiveAffineCutoff Aref |Option J × I| |I| ε p (scalarTransferTail (3p)) Z (scalarTransferBaseAccuracy (3p)) Z` (a natural number), and $\mathrm{cellLog}$ = `scalarTransferCellLog common b p Z U` (all explicit functions defined by OpenAI).
--
--   **Further hypotheses.** $(p_{\mathrm{ref}} + 2)^E \le \mathrm{budget}$; $p + \texttt{scalarTransferTail}(3p) + 4 \le \mathrm{budget}$; `scalarTransferAccuracyLog b p Z` $\le \mathrm{meshLog}$. Let $\mathrm{lo} : I \to \mathbb{Z}$, $N : I \to \mathbb{N}$, $H : I \to \mathbb{R}$ and reals $\rho, L, C, B, A, c, \mathrm{sourceRatio}, \mathrm{parameterRatio}$ with $\rho > 0$, $L \ge 1$, $H(i) > 0$, $C, B, A \ge 0$, $c > 0$, $\mathrm{sourceRatio}, \mathrm{parameterRatio} \ge 0$, $\rho^{-1} \le e^{\mathrm{gridLog}}$, $A \le e^{\mathrm{ratioLog}}$; for all $i$: $4 \le \rho H(i) \le 2N(i)$, $N(i) \le A H(i)$, and $4\exp(\mathrm{gridLog} + \max((p_{\mathrm{ref}}+2)^E, \mathrm{cellLog})) \le H(i)$. Let $\mathcal{P}$ = `normalizedBoxPartitions N H rho …` (OpenAI's box partitions, positive by an accompanying lemma). Assume $g(z)$ (that is, `g.eval z`) is real with $0 \le \operatorname{Re} g(z) \le 1$ for every $z$ in the box $\mathrm{lo} + \prod_i [0, N(i))$ (`translatedIntegerBox lo N`). Let $h : \mathbb{Z}^I \to \mathbb{C}$ with $0 \le \operatorname{Re} h(z) \le 1$ on that box, and assume `ResidueSliceUpperComparison h g.eval lo N budget level (exp (-budget))` (OpenAI: on every physical sub-box and residue slice of log-cost at most budget, the real part of the residue mean of $h$ is at most level times that of $g$ plus $e^{-\mathrm{budget}}$). Let $\mathrm{sourceLo} < \mathrm{sourceHi}$ be integer functions on $\texttt{Option}\ J \times I$ and $\mathrm{parLo} < \mathrm{parHi}$ integer functions on $J$, with:
--   - $c H(i) \le \mathrm{sourceHi}(\mathrm{none}, i) - \mathrm{sourceLo}(\mathrm{none}, i)$;
--   - $\lvert(\mathrm{anchor}(j) + D\,\mathrm{parLo}(j))/L\rvert \le C$ and $\lvert(\mathrm{anchor}(j) + D\,\mathrm{parHi}(j))/L\rvert \le C$;
--   - $\lvert\mathrm{sourceLo}(\mathrm{some}\ j, i)\rvert \le BH(i)/L$ and $\lvert\mathrm{sourceHi}(\mathrm{some}\ j, i)\rvert \le BH(i)/L$;
--   - $40\lvert I\rvert A/(\rho c) \le e^{\mathrm{meshLog}}$, $1 + \lvert J\rvert(C + B) \le e^{\mathrm{meshLog}}$, $\mathrm{sourceRatio} \le e^{\mathrm{meshLog}}$, $\mathrm{parameterRatio} \le e^{\mathrm{meshLog}}$;
--   - `smoothPairCoefficientScale (H z₂) L z₁` $\le \mathrm{sourceRatio} \cdot (\mathrm{sourceHi}(z) - \mathrm{sourceLo}(z))$ for every $z = (z_1, z_2)$, and $L/D \le \mathrm{parameterRatio} \cdot (\mathrm{parHi}(j) - \mathrm{parLo}(j))$ for every $j$;
--   - $4\exp(4\,\mathrm{meshLog} + 18 + \mathrm{cellLog} + Z) \le L$ and $4\exp(4\,\mathrm{meshLog} + 18 + \mathrm{cellLog}) L^{\lvert J\rvert + 1} \le H(i)$ for every $i$.
--
--   For $t \in \prod_j [\mathrm{parLo}(j), \mathrm{parHi}(j))$ and $z \in \prod [\mathrm{sourceLo}, \mathrm{sourceHi})$ write $\mathrm{pt}(t, z)$ = `smoothAffineSample (j ↦ anchor j + D t_j) z`, the point $i \mapsto z(\mathrm{none}, i) + \sum_j (\mathrm{anchor}(j) + D t_j) z(\mathrm{some}\ j, i)$. Assume the two base-accuracy hypotheses: for $F = \operatorname{Re} h$ and for $F = \operatorname{Re} g$, and for every weight $w$ with $0 \le w \le 1$ on the source box,
--   $$\Bigl\lvert \mathbb{E}_{t, z}\bigl[w(z) \cdot \texttt{physicalBoxResidual lo N P hpos}\ (i \mapsto \mathrm{prime}(i)^{\mathrm{power}(i)})\ b\ F\ (\mathrm{pt}(t,z))\bigr]\Bigr\rvert \le \texttt{scalarTransferBaseAccuracy}(3p),$$
--   where $(t, z)$ is uniform on the product of the parameter box and the source box (`integerBoxUniformWeights`).
--
--   **Conclusion.** For every finite probability law `outer` on the source box whose weights are at most $e^p$ times the uniform weights, the `outer`-probability of the event
--   $$e^{-p} < \mathbb{E}_{t}\Bigl[\bar h(\mathrm{pt}(t, z)) - (1 + \varepsilon)\,\mathrm{level}\cdot \bar g(\mathrm{pt}(t, z))\Bigr]$$
--   is at most $e^{-p}$, where $t$ is uniform on the parameter box and $\bar h$, $\bar g$ are $\operatorname{Re} h$ and $\operatorname{Re} g$ extended by zero outside the box `translatedIntegerBox lo N` (`realZeroExtendFinset`).
--
--   Lean: `OAI.Erdos3.exists_niltest_geometric_scalar_transfer_s2`, which states OpenAI's `OAI.Erdos3.exists_niltest_geometric_scalar_transfer` (in `lean/OAI/Combinatorics/Progressions/Nilpotent/NiltestScalarTransfer.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B218` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Nilpotent/NiltestScalarTransfer.lean (declaration OAI.Erdos3.exists_niltest_geometric_scalar_transfer)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_geometric_scalar_transfer_s2 (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {I : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype I] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p epsilon Z U gridLog ratioLog meshLog level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ Z → 0 ≤ U → 0 ≤ meshLog →
    p ≤ U → scalarTransferTail (3 * p) ≤ U → Z ≤ U →
    gridLog + ratioLog + 2 ≤ U → epsilon⁻¹ ≤ Real.exp U →
    Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ U → (Fintype.card (Option J × I) : ℝ) ≤ U →
    (Fintype.card J : ℝ) ≤ U → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (Fintype.card ι : ℝ) ≤ Real.exp Z →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp Z) →
    ∀ (D : ℕ) (anchor : J → ℤ), 0 < D → (D : ℝ) ≤ Real.exp Z →
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let Aref := ⌈(pref + 2) ^ E⌉₊
    let b := adaptiveAffineCutoff Aref (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon p (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let _beta := scalarTransferMarginalAccuracy (3 * p) (scalarTransferCapLog b Z)
    let cellLog := scalarTransferCellLog common b p Z U
    (pref + 2) ^ E ≤ budget → p + scalarTransferTail (3 * p) + 4 ≤ budget →
    scalarTransferAccuracyLog b p Z ≤ meshLog →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ)
      (rho L C B A c sourceRatio parameterRatio : ℝ),
    0 < rho → 1 ≤ L → (∀ i, 0 < H i) → 0 ≤ C → 0 ≤ B → 0 ≤ A → 0 < c →
    0 ≤ sourceRatio → 0 ≤ parameterRatio → rho⁻¹ ≤ Real.exp gridLog → A ≤ Real.exp ratioLog →
    ∀ (hsiteLarge : ∀ i, 4 ≤ rho * H i) (hsiteWhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ)),
    (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ i, 4 * Real.exp (gridLog + max ((pref + 2) ^ E) cellLog) ≤ H i) →
    let P := normalizedBoxPartitions N H rho hsiteLarge hsiteWhole
    let hpos := normalizedBoxPartitions_positive N H rho hsiteLarge hsiteWhole
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z)
      (parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    (∀ i, c * H i ≤ ((sourceHi (none,i) - sourceLo (none,i) : ℤ) : ℝ)) →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    40 * (Fintype.card I : ℝ) * A / (rho * c) ≤ Real.exp meshLog →
    1 + (Fintype.card J : ℝ) * (C + B) ≤ Real.exp meshLog →
    sourceRatio ≤ Real.exp meshLog → parameterRatio ≤ Real.exp meshLog →
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      sourceRatio * ((sourceHi z - sourceLo z).toNat : ℝ)) →
    (∀ j, L / (D : ℝ) ≤ parameterRatio * ((parHi j - parLo j).toNat : ℝ)) →
    4 * Real.exp (4 * meshLog + 18 + cellLog + Z) ≤ L →
    (∀ i, 4 * Real.exp (4 * meshLog + 18 + cellLog) * L ^ (Fintype.card J + 1) ≤ H i) →
    (∀ w : (Option J × I → ℤ) → ℝ,
      (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
        0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights parLo parHi hpar).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
        (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hpos
          (fun i => prime i ^ power i) b (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤
        scalarTransferBaseAccuracy (3 * p)) →
    (∀ w : (Option J × I → ℤ) → ℝ,
      (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
        0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights parLo parHi hpar).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
        (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hpos
          (fun i => prime i ^ power i) b (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤
        scalarTransferBaseAccuracy (3 * p)) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  sorry

end Erdos3

end

end OAI
end
