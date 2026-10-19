-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_niltest_mesh_scalar_transfer_s2
-- name    : OAI.Erdos3.exists_niltest_mesh_scalar_transfer_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:51:47.236628+00:00
-- url     : https://prove2.me/theorems/d2ebe4ee-1ef8-41fe-858b-48e9e0c2e24e
-- title:
--   Mesh scalar transfer of a niltest upper comparison to random affine samples
-- statement:
--   For every $s \in \mathbb{N}$ there is $E \in \mathbb{N}$ with $2 \le E$ such that the following holds. Let $\iota$ be a finite linearly ordered type and $I, J$ finite types; let $V$ be a Lie algebra over $\mathbb{Q}$ such that $\mathbb{R} \otimes_{\mathbb{Q}} V$ carries a topology making it a Hausdorff topological additive group with continuous real scalar multiplication; let $d \in \mathbb{N}$ and `nilmanifold : RationalFilteredNilmanifold V s d` (a structure bundling a nilpotent Lie filtration of step $s$, a $\mathbb{Q}$-basis indexed by $\mathrm{Fin}\ d$, layer bases, a lattice subgroup and a positive grid parameter). Let $p, \epsilon, L, T, C, \mathrm{totalShell}, \mathrm{modLog}, \mathrm{dimLog}, \mathrm{sourceDimLog}, \mathrm{level} \in \mathbb{R}$ with $2 \le p$, $0 < \epsilon$, $0 \le L$, $0 \le T$, $0 \le C$, $0 < \mathrm{totalShell}$, $0 \le \mathrm{modLog} \le p$, $0 \le \mathrm{dimLog}$, $0 \le \mathrm{sourceDimLog}$, $T + 4 \le p$, $e^{-L} \le \mathrm{level} \le 2$, $|I| \le p$, $|\iota| \le e^{C}$, $|I| \le e^{\mathrm{dimLog}}$, $|\mathrm{Option}\ J \times I| \le e^{\mathrm{sourceDimLog}}$ and $2 \le |J|$. Let `g : nilmanifold.Niltest (fun _ : I => 1)` (a polynomial orbit with all weights $1$ and a bounded Lipschitz complex observable) with `g.ComplexityLE p`. Let $\mathrm{prime}, \mathrm{power} : \iota \to \mathbb{N}$ with every $q_i := \mathrm{prime}(i)^{\mathrm{power}(i)}$ nonzero, every $\mathrm{prime}(i)$ prime, $\mathrm{prime}$ injective and $q_i \le e^{\mathrm{modLog}}$. Let $D \in \mathbb{N}$ and $\mathrm{anchor} : J \to \mathbb{Z}$ with $|$`affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D`$| \le p$ (a finite set of indices in $\iota$) and `affineRemovalDepth T + affineComparisonTail ε L T` $\le p$ (natural numbers). Let $\mathrm{lo} : I \to \mathbb{Z}$, $N : I \to \mathbb{N}$ and, for each $i$, `P i : FiniteProgressionPartition (N i)` (a structure partitioning $\{0, \dots, N_i - 1\}$ into labelled arithmetic progressions with a start, a positive step and a length per label) with all steps $1$ and all lengths positive; assume `g.eval z` is real and in $[0,1]$ for $z$ in the box $X = \prod_i [\mathrm{lo}_i, \mathrm{lo}_i + N_i)$ and $e^{-p} N_i \le$ the length of every cell of $P_i$. Let $h : \mathbb{Z}^I \to \mathbb{C}$ with $0 \le \mathrm{Re}\,h \le 1$ on $X$ and `ResidueSliceUpperComparison h g.eval lo N ((p + 2) ^ E) level (affineIncrementTolerance L T)` (`affineIncrementTolerance L T` $= e^{-(L+T+4)}$). Let $\mathrm{sourceLo}, \mathrm{sourceHi} : \mathrm{Option}\ J \times I \to \mathbb{Z}$ with $\mathrm{sourceLo} < \mathrm{sourceHi}$ coordinatewise and progression partitions $S_{\mathbf i}$ of $\{0, \dots, \mathrm{sourceHi}_{\mathbf i} - \mathrm{sourceLo}_{\mathbf i} - 1\}$ with all steps $1$ and all lengths positive. Put $A = \lceil (p+2)^E \rceil$ and $B = $ `adaptiveAffineCutoff A |Option J × I| |I| ε L T C totalShell modLog` (a natural number), and assume every cell of every $P_i$ has length at least $\exp\max\big((p+2)^E,\ $`adaptiveAffineSideLog A |Option J × I| |I| ε L T C totalShell modLog dimLog`$\big)$ and every cell of every $S_{\mathbf i}$ has length at least $\exp($`adaptiveAffineSideLog` with the same arguments but $\mathrm{sourceDimLog}$ in place of $\mathrm{dimLog})$. Let $\mathrm{paramLo}, \mathrm{paramHi} : J \to \mathbb{Z}$ with $\mathrm{paramLo} < \mathrm{paramHi}$ coordinatewise and progression partitions $T_j$ (`paramPartition j`) of $\{0, \dots, \mathrm{paramHi}_j - \mathrm{paramLo}_j - 1\}$ with all steps $1$ and all lengths positive. Let $\eta_{\mathrm{param}}, \eta_{\mathrm{site}}, \beta, \mathrm{accuracy} \in \mathbb{R}$ with $\eta_{\mathrm{param}}, \eta_{\mathrm{site}} \ge 0$, and assume:
--
--   - for every product cell $c_t$ of the $T_j$ (with lower corner `intervalCellLower`, i.e. $\mathrm{paramLo}_j$ plus the cell start), `ProductMarginalsClose (primeCoordinateReference q) ρ etaParam B` holds, where $\rho$ is `residuePrimeCoordinateDensity` of that cell with modulus $M = 1$, residue $0$, the moduli $q$ and the constant function $1$, and likewise for every product cell $c$ of the $P_i$ with $\eta_{\mathrm{site}}$; here `primeCoordinateReference q` is the family of uniform laws on $(\cdot \to \mathbb{Z}/q_i)$, `residuePrimeCoordinateDensity` is the density, relative to that product law, of the distribution of the coordinatewise reductions mod $q_i$ of a uniform point of the cell, and `ProductMarginalsClose μ ρ η B` says that for every set of at most $B$ indices and every point of positive product weight, OpenAI's `productConditionalMean` of $\rho$ on that set differs from $1$ by at most $\eta$;
--   - under the product of the uniform laws on the parameter box $\prod_j [\mathrm{paramLo}_j, \mathrm{paramHi}_j)$ and the source box $\prod_{\mathbf i} [\mathrm{sourceLo}_{\mathbf i}, \mathrm{sourceHi}_{\mathbf i})$, the probability of `physicalMeshCrossing lo N P mesh location` is at most $\beta$, where `mesh` sends $(t, z)$ to the pair of `integerBoxMesh` cells of $z$ (for the $S$) and of $t$ (for the $T$), `location` sends $(t, z)$ to $x_t(z) := $ `smoothAffineSample (anchor + D t) z` ($x_t(z)_i = z_{(\mathrm{none},i)} + \sum_j (\mathrm{anchor}_j + D t_j) z_{(\mathrm{some}\ j, i)}$), and the crossing event is that some $(t', z')$ in the same mesh cell has location in a different `physicalBoxClassify` cell of the $P$;
--   - for every $w : \mathbb{Z}^{\mathrm{Option}\ J \times I} \to \mathbb{R}$ with values in $[0,1]$ on the source box, the absolute value of the mean, under that product law, of $w(z)\cdot$`physicalBoxResidual lo N P _ q B (Re h)` $(x_t(z))$ is at most $\mathrm{accuracy}$, and likewise with $\mathrm{Re}\,$`g.eval` in place of $\mathrm{Re}\,h$ (`physicalBoxResidual` is $f$ minus OpenAI's `physicalBoxTruncation` on $X$ and $0$ off $X$).
--
--   Let $p_{\mathrm{target}}, \mathrm{dominationLog} \in \mathbb{R}$ and let `outer` be a probability law (`FiniteProbabilityWeights`) on the source box whose weight is everywhere at most $e^{\mathrm{dominationLog}}$ times the uniform weight, and assume
--   $$100(1+\epsilon)e^{-T/2} + (1+\epsilon)\mathrm{totalShell} + (1 + (1+\epsilon)\mathrm{level})\big((\eta_{\mathrm{param}} + \beta)\,\mathrm{residueTruncationCap}(\iota, B, \eta_{\mathrm{site}}) + \mathrm{accuracy}\big) \le e^{-(2p_{\mathrm{target}} + \mathrm{dominationLog})}/2,$$
--   where `residueTruncationCap ι B η` is the number of OpenAI's `lowDegreeCoordinateSets ι B` times $2^B(1+\eta)$. Then the `outer`-probability of the event that $e^{-p_{\mathrm{target}}} < \mathbb{E}_t\big[\bar h(x_t(z)) - (1+\epsilon)\,\mathrm{level}\,\bar g(x_t(z))\big]$, with $t$ uniform on the parameter box and $\bar h, \bar g$ the real parts of $h$ and `g.eval` on $X$ extended by $0$ (`realZeroExtendFinset`), is at most $e^{-p_{\mathrm{target}}}$.
--
--   `ResidueSliceUpperComparison h g parent H P level ε` says: for every $\mathrm{lo}', N', M > 0, u$ with `PhysicalSubbox parent H lo' N'` (the box $\prod_j[\mathrm{lo}'_j, \mathrm{lo}'_j + N'_j)$ lies in $\prod_j[\mathrm{parent}_j, \mathrm{parent}_j + H_j)$) and `ResidueSliceLogCostLE H lo' N' M u P` (each $e^{-P} H_j$ is at most the number of integers in $[\mathrm{lo}'_j, \mathrm{lo}'_j + N'_j)$ congruent to $u_j$ mod $M$), the real part of `physicalResidueMean h lo' N' M u` (the average of $h$ over the points of that box congruent to $u$ mod $M$) is at most $\mathrm{level}$ times that of $g$ plus $\varepsilon$. `g.eval z` is the observable at the image of the polynomial orbit at $z$; `g.ComplexityLE p` says the geometry of the nilmanifold has complexity at most $p$ and $\log(2 + \text{normBound} + \text{lipBound}) \le p$.
--
--   Lean: `OAI.Erdos3.exists_niltest_mesh_scalar_transfer_s2`, which states OpenAI's `OAI.Erdos3.exists_niltest_mesh_scalar_transfer` (in `lean/OAI/Combinatorics/Progressions/Nilpotent/NiltestScalarTransfer.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B218` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Nilpotent/NiltestScalarTransfer.lean (declaration OAI.Erdos3.exists_niltest_mesh_scalar_transfer)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_mesh_scalar_transfer_s2 (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {I : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype I] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p epsilon L T C totalShell modLog dimLog sourceDimLog level : ℝ),
    2 ≤ p → 0 < epsilon → 0 ≤ L → 0 ≤ T → 0 ≤ C → 0 < totalShell →
    0 ≤ modLog → modLog ≤ p → 0 ≤ dimLog → 0 ≤ sourceDimLog → T + 4 ≤ p →
    Real.exp (-L) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → (Fintype.card ι : ℝ) ≤ Real.exp C →
    (Fintype.card I : ℝ) ≤ Real.exp dimLog →
    (Fintype.card (Option J × I) : ℝ) ≤ Real.exp sourceDimLog → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp modLog) →
    ∀ (D : ℕ) (anchor : J → ℤ),
    ((affineSamplerPrimeMask prime (epsilon / (2 + epsilon)) (affineComparisonScale epsilon L T C) 1 1 D).card : ℝ) ≤ p →
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ p →
    ∀ (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)),
    (∀ i c, (P i).step c = 1) → ∀ (hPpos : ∀ i c, 0 < (P i).length c),
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    (∀ i c, Real.exp (-p) * (N i : ℝ) ≤ ((P i).length c : ℝ)) →
    ∀ (h : (I → ℤ) → ℂ),
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N ((p + 2) ^ E) level (affineIncrementTolerance L T) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ)
      (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat),
    (∀ i cs, (S i).step cs = 1) → ∀ (_hSpos : ∀ i cs, 0 < (S i).length cs),
    ∀ (hsource : ∀ i, sourceLo i < sourceHi i),
    let A := ⌈(p + 2) ^ E⌉₊
    let B := adaptiveAffineCutoff A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog
    (∀ i c, Real.exp (max ((p + 2) ^ E)
      (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
        epsilon L T C totalShell modLog dimLog)) ≤ ((P i).length c : ℝ)) →
    (∀ i cs, Real.exp (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog sourceDimLog) ≤ ((S i).length cs : ℝ)) →
    ∀ (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
      (paramPartition : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat),
    (∀ j c, (paramPartition j).step c = 1) →
    ∀ (hTpos : ∀ j c, 0 < (paramPartition j).length c),
    ∀ (etaParam etaSite beta accuracy : ℝ), 0 ≤ etaParam → 0 ≤ etaSite →
    ∀ (_hcloseParam : ∀ ct : (∀ j, (paramPartition j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) (fun i => prime i ^ power i))
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (paramPartition j) (ct j))
          (fun j => (paramPartition j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) paramPartition hTpos ct)
          (fun i => prime i ^ power i) (fun _ => 1)) etaParam B)
    (_hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) (fun i => prime i ^ power i))
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          (fun i => prime i ^ power i) (fun _ => 1)) etaSite B)
    (_hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi paramPartition tz.1))
        (fun tz => smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta)
    (_heh : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos (fun i => prime i ^ power i) B (fun z => (h z).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (_heg : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos (fun i => prime i ^ power i) B (fun z => (g.eval z).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (pTarget dominationLog : ℝ)
    (outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)))
    (_hdom : ∀ z, outer.weight z ≤ Real.exp dominationLog *
      (integerBoxUniformWeights sourceLo sourceHi hsource).weight z)
    (_herror : (100 * (1 + epsilon) * Real.exp (-T / 2) + (1 + epsilon) * totalShell) + (1 + ((1 + epsilon) * level)) * ((etaParam + beta) * residueTruncationCap ι B etaSite + accuracy) ≤
      Real.exp (-(2 * pTarget + dominationLog)) / 2),
    outer.eventProbability (fun z => Real.exp (-pTarget) <
      (integerBoxUniformWeights paramLo paramHi hparam).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        ((1 + epsilon) * level) * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤
      Real.exp (-pTarget) := by
  sorry

end Erdos3

end

end OAI
end
