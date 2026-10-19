-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_unconditioned_joint_scalar_transfer_s2
-- name    : OAI.Erdos3.exists_unconditioned_joint_scalar_transfer_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:06:04.668776+00:00
-- url     : https://prove2.me/theorems/ab9e4996-e51e-4ad2-b385-1f92c86c8b9e
-- title:
--   Under a residue slice upper comparison, a smooth random affine sample rarely sees a large positive excess of h over (1+ε)·level·g
-- statement:
--   Let $s$ be a natural number. Then there is a natural number $E \ge 2$ with the following property. (All named objects are defined by OpenAI.) Let $I$ be a finite type (in a universe $u$), $J$ a finite type, and $V$ a Lie algebra over $\mathbb{Q}$ (in a universe $v$) with a topology on $\mathbb{R} \otimes_{\mathbb{Q}} V$ making it a Hausdorff topological additive group with continuous real scalar multiplication. Let $d_0$ be a natural number and `nilmanifold` a `RationalFilteredNilmanifold V s d₀`. Let $p, \varepsilon, P_0, \mathrm{level}, \mathrm{budget}$ be reals with $p \ge 2$, $0 < \varepsilon \le 1$, $P_0 \ge 0$, $3p + 10 \le P_0$, $\varepsilon^{-1} \le e^{P_0}$, $e^{-p} \le \mathrm{level} \le 2$, $\#I \le p$, $2 \le \#J \le e^{P_0}$, and `probabilityProfileLipschitz` $\le e^{P_0}$ (the Lipschitz constant fixed by OpenAI for its smooth probability profile $\psi$). Let $g$ be a niltest on `nilmanifold` with variables $I$, each of weight $1$, of complexity at most $p$; write $g(z)$ for its evaluation at $z \in \mathbb{Z}^I$. Let $k_0 \in J$, let $D$ be a natural number, and $\mathrm{anchor}, \mathrm{parLo}, \mathrm{parHi} : J \to \mathbb{Z}$ with $\mathrm{parLo}(j) < \mathrm{parHi}(j)$ for all $j$; assume $0 < D \le e^{P_0}$. Let $L, C, B, A, K, c, C_{\mathrm{width}}$ be reals with $1 \le C$, $B, A, K \ge 0$, $c > 0$, $C_{\mathrm{width}} \ge 0$, and $C, B, A, K, c^{-1}, C_{\mathrm{width}}$ all at most $e^{P_0}$.
--
--   Let $\mathrm{lo} : I \to \mathbb{Z}$, $N : I \to \mathbb{N}$ and $H : I \to \mathbb{R}$ with $H(i) \le 2N(i)$ and $N(i) \le A\, H(i)$ for all $i$, and let $\mathcal{B}$ = `translatedIntegerBox lo N` $= \mathrm{lo} + \prod_i ([0, N(i)) \cap \mathbb{Z})$. Assume $g(z)$ is real with $0 \le g(z) \le 1$ for $z \in \mathcal{B}$. Let $h : \mathbb{Z}^I \to \mathbb{C}$ with $0 \le \operatorname{Re} h(z) \le 1$ for $z \in \mathcal{B}$, and assume `ResidueSliceUpperComparison h g lo N budget level (exp(-budget))` (OpenAI: for every physical subbox of $\mathcal{B}$ and every residue slice of log-cost at most $\mathrm{budget}$, the real part of the residue mean of $h$ is at most $\mathrm{level}$ times that of $g$ plus $e^{-\mathrm{budget}}$). Let $R$ be a natural number and $\mathrm{parMin} > 0$ with $\mathrm{parMin} \le \mathrm{parHi}(j) - \mathrm{parLo}(j) \le R$ for all $j$, $R \le C_{\mathrm{width}}\, \mathrm{parMin}$, $cL \le \mathrm{parMin}$, and $|(\mathrm{anchor}(j) + D\, \mathrm{parLo}(j))/L| \le C$ and $|(\mathrm{anchor}(j) + D\, \mathrm{parHi}(j))/L| \le C$ for all $j$.
--
--   Let $\mathrm{origin}, \mathrm{sourceLo}, \mathrm{sourceHi} : \operatorname{Option} J \times I \to \mathbb{Z}$ with $\mathrm{sourceLo} < \mathrm{sourceHi}$ pointwise. Write $\mathrm{sc}(c', i)$ = `smoothPairCoefficientScale (H i) L c'`, equal to $H(i)$ for $c' = \mathrm{none}$ and $H(i)/L$ for $c' = \mathrm{some}\ j$. Assume $\mathrm{sc}(z) \le K(\mathrm{sourceHi}(z) - \mathrm{sourceLo}(z))$ for all $z$; $|w(z) - \mathrm{origin}(z)| \le \mathrm{sc}(z)/2$ for every $w$ in the box $\prod_z [\mathrm{sourceLo}(z), \mathrm{sourceHi}(z))$ and every $z$; and $|\mathrm{sourceLo}(\mathrm{some}\ j, i)| \le B H(i)/L$ and $|\mathrm{sourceHi}(\mathrm{some}\ j, i)| \le B H(i)/L$ for all $j, i$.
--
--   Put $m = \#(\operatorname{Option} J \times I)$, $n = \#I$, $d = \#J$, $Z$ = `replacementCommonInputLog m n d P0`, $G = 2 \cdot \texttt{physicalPairCoefficientLog n d Z} + 2$, $U$ = `scalarInitialReferenceInput m n d p P0`, $\mathrm{pref}$ = `affineReferenceInput ε U`, $\mathrm{common}$ = `affineCommonReferenceBudget E ε U`, $b$ = `adaptiveAffineCutoff ⌈(pref + 2)^E⌉ m n ε p (scalarTransferTail (3p)) Z (scalarTransferBaseAccuracy (3p)) Z` (natural-number ceiling), $\mathrm{cellLog}$ = `scalarTransferCellLog common b p Z U`, and $\mathrm{meshLog}$ = `scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)`. Assume `scalarCombinedLogThreshold n d b p P0 Z G ((pref + 2)^E) cellLog meshLog` $\le \mathrm{budget}$, $e^{\mathrm{budget}} \le L$, and $e^{\mathrm{budget}} L^{d+1} \le H(i)$ for all $i$.
--
--   Let $\mathrm{bases}$ be a nonempty finite set of points of $\mathbb{Z}^I$, $\mathrm{width} : \operatorname{Option} J \times I \to \mathbb{R}$ positive, with $\sum_{z} \prod_{t} \psi(z(t)/\mathrm{width}(t)) > 0$ (the sum over all $z : \operatorname{Option} J \times I \to \mathbb{Z}$ of `selectedResidueSmoothWeight (fun _ => 1) {0} width z`, modulus $1$ and the single residue cell $0$), and $8 \cdot \texttt{probabilityProfileLipschitz} \le \mathrm{width}(\mathrm{some}\ j, i)$ for all $(j, i)$. Assume (_hframe) for every base $a \in \mathrm{bases}$, every $w$ in `rectangularWeightIndices 0 width 1` and every $t = (c', i)$, the frame value `jointIntegerFrame (a, w) c' i` (equal to $a(i) + w(\mathrm{none}, i)$ if $c' = \mathrm{none}$ and $w(\mathrm{some}\ j, i)$ if $c' = \mathrm{some}\ j$) lies in $[\mathrm{sourceLo}(t), \mathrm{sourceHi}(t))$. Assume finally
--   $$\prod_t (\mathrm{sourceHi}(t) - \mathrm{sourceLo}(t)) \cdot \Bigl( (\#\mathrm{bases})^{-1} \prod_{(j,i) \in J \times I} \frac{2}{\mathrm{width}(\mathrm{some}\ j, i)} \Bigr) \le e^p.$$
--
--   Then, under the probability weights `selectedJointReference bases _ (fun _ => 1) {0} width _ _` on pairs $(a, w)$ (uniform $a \in \mathrm{bases}$ times the law on $w \in$ `rectangularWeightIndices 0 width 1` proportional to $\prod_t \psi(w(t)/\mathrm{width}(t))$), the probability of the event
--   $$e^{-p} < \mathbb{E}_{\theta}\Bigl[ \bar h\bigl(y_\theta(a, w)\bigr) - (1+\varepsilon)\, \mathrm{level}\, \bar g\bigl(y_\theta(a, w)\bigr) \Bigr]$$
--   is at most $e^{-p}$. Here $\theta$ is uniform on $\prod_j [\mathrm{parLo}(j), \mathrm{parHi}(j))$ (`integerBoxUniformWeights`), $y_\theta(a, w)$ = `smoothAffineSample (fun j => anchor j + D θ_j) F` with $F$ the frame `jointIntegerFrame (a, w)`, i.e. $y_\theta(a,w)(i) = F(\mathrm{none}, i) + \sum_j (\mathrm{anchor}(j) + D\theta_j) F(\mathrm{some}\ j, i)$, and $\bar h, \bar g$ are $\operatorname{Re} h$ and $\operatorname{Re} g$ on $\mathcal{B}$, extended by $0$ outside $\mathcal{B}$ (`realZeroExtendFinset`).
--
--   Lean: `OAI.Erdos3.exists_unconditioned_joint_scalar_transfer_s2`, which states OpenAI's `OAI.Erdos3.exists_unconditioned_joint_scalar_transfer` (in `lean/OAI/Combinatorics/Progressions/Estimates/CanonicalUnconditionedScalarTransfer.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B151` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/CanonicalUnconditionedScalarTransfer.lean (declaration OAI.Erdos3.exists_unconditioned_joint_scalar_transfer)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151

section

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_unconditioned_joint_scalar_transfer_s2 (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → 2 ≤ Fintype.card J →
    (Fintype.card J : ℝ) ≤ Real.exp P0 →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (_k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (origin sourceLo sourceHi : Option J × I → ℤ) (_hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    let m := Fintype.card (Option J × I)
    let n := Fintype.card I
    let d := Fintype.card J
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
      (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let cellLog := scalarTransferCellLog common b p Z U
    let meshLog := scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)
    scalarCombinedLogThreshold n d b p P0 Z G ((pref + 2) ^ E) cellLog meshLog ≤ budget →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (d + 1) ≤ H i) →
    ∀ (bases : Finset (I → ℤ)) (hbases : bases.Nonempty)
      (width : Option J × I → ℝ) (hwidth : ∀ z, 0 < width z)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    (∀ z : J × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some z.1,z.2)) →
    ∀ _hframe : ∀ z : bases × rectangularWeightIndices 0 width 1, ∀ t,
      jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈ Finset.Ico (sourceLo t) (sourceHi t),
    ((∏ t, ((sourceHi t - sourceLo t : ℤ) : ℝ)) *
      ((bases.card : ℝ)⁻¹ * ∏ t : J × I, 2 / width (some t.1,t.2))) ≤ Real.exp p →
    (selectedJointReference bases hbases (fun _ : I => 1) {0} width hwidth hZ).eventProbability
      (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  sorry

end Erdos3

end

end OAI
end
