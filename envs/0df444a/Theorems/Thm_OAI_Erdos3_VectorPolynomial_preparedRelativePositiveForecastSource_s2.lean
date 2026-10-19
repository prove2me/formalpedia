-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativePositiveForecastSource_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedRelativePositiveForecastSource_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:28:25.306596+00:00
-- url     : https://prove2.me/theorems/8df3803b-f0c9-4754-9b3b-ed5c9f8b8c26
-- title:
--   All-degree native detection for a nested forward schedule yields degree-0 native detection with the augmented unit threshold and an excess-mass bound
-- statement:
--   All named objects below are defined by OpenAI.
--
--   **Data.** Let $m$ be a natural number, $G, X$ finite types, $I_j, J_j$ ($j<m$) finite types, $n : \mathrm{Fin}(m)\to\mathbb{N}$, $B_a$ finite types indexed by `LayerSamplerAxis I n`, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, `b j` bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)` with $\mathbb{Z}$-span the projected integer lattice (`hb`), $R, \sigma$ with $R_j > 0$, $\sigma_j > 0$, `S : LayerSamplerScale B U b R σ`, orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$, $N : X \to \mathbb{N}$, vector polynomials `poly j : VectorPolynomial X ℝ (J j → ℝ)` with coefficients in $U_j$, reals $\tau, \xi$, `stride : X → ℕ`, a finite set `cells` of column residue patterns, a point `center` of the coefficient torus, and assume each lattice section of $\mathbb{Z}^{J_j}$ in `euclideanSubspace (U j)` is a $\mathbb{Z}$-lattice. Let `A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center` (OpenAI's external candidate sampler; `A.NativeDetection` is its native-detection property, treated as opaque here).
--
--   Let $s, A_{\exp}, C_{\mathrm{direct}}, C_{\mathrm{slice}}$ be natural numbers, `constants : ℕ → ℕ`, reals $B_{\mathrm{struct}}, \mathrm{gainLog}, \mathrm{stageLog}, P_{\mathrm{late}}$, and $P_{\mathrm{master}}$ a real function on the slot type $\mathcal{K}$ = `PreparedFiniteNestedForwardAllDegreeSlot (2s+2) (s+1) s`. For $k \in \mathcal{K}$ write $\deg k$ = `preparedFiniteNestedForwardAllDegreeDegree k`, $\mathrm{st}(k)$ = `(preparedFiniteNestedForwardAllDegreeStage k).val`, $\mathrm{sd}(k)$ = `preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k`, and $\mathrm{nb}(k)$ = `(preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (deg k)) (deg k + 1) (Pmaster k) Plate).nativeBudget`.
--
--   **Hypotheses.**
--   - (`hdirect`) For every $k \in \mathcal{K}$, `A.NativeDetection` holds with degree $\deg k$, slice parameter $(\texttt{preparedFiniteForwardParameter Aexp constants st(k) sd(k)} + C_{\mathrm{slice}})^{C_{\mathrm{slice}}}$, test parameter equal to the real evaluation of the polynomial `preparedFiniteForwardDetectorPolynomial s` at `allocatedModelTestLog (preparedFiniteForwardPairedSourcePrecision Aexp Cdirect constants st(k) (preparedFiniteNestedForwardAllDegreeIsDirect k) sd(k) gainLog stageLog) (preparedFiniteForwardWork Aexp constants st(k) sd(k))`, budget $\mathrm{nb}(k)$, and threshold `preparedFiniteNestedForwardFixedCenterThreshold Aexp constants Bstruct gainLog stageLog k`.
--   - $A_{\exp} \ge 2$; $B_{\mathrm{struct}} \ge 0$; $\mathrm{gainLog}, \mathrm{stageLog} \in [0, B_{\mathrm{struct}}]$.
--   - Two proofs that $\xi \le 1$ (`hξsource`, `hξtarget`) and two proofs (`hmarginSource`, `hmarginTarget`) that $2\cdot$`spatialTrimMargin τ N x` $\le N_x$ for all $x$.
--   - Reals `knob`, `rawCap`, `capLog`.
--
--   **Abbreviations.** $\mathrm{seed}$ = `candidateNestedForwardSeed Aexp constants (s+1) (2s+2) Bstruct`; $u$ = `preparedFiniteForwardModelPrecision Aexp constants (s+1) seed gainLog stageLog`; $p$ = `preparedFiniteForwardWork Aexp constants (s+1) seed`; $\mathrm{sliceLog} = (\texttt{preparedFiniteForwardParameter Aexp constants (s+1) seed} + C_{\mathrm{slice}})^{C_{\mathrm{slice}}}$; $\mathrm{testLog}$ = the real evaluation of `preparedFiniteForwardDetectorPolynomial s` at `allocatedModelTestLog (preparedFiniteForwardSourcePrecision Aexp constants (s+1) seed gainLog stageLog) p`; $\mathrm{native}$ = `(preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) 1 (Pmaster anchor) 0).nativeBudget` with anchor = `preparedFiniteNestedForwardAllDegreeAnchor (2s+2) (s+1) s`; $E_{\mathrm{cond}}$ = `preparedNestedFrontProjectionEnvelope Aexp constants (s+1) (k ↦ k.1.val) (k ↦ k.2.1.val) nb Bstruct gainLog stageLog knob`. Let $V = |\texttt{LayerSamplerVariables G I n B}|$, and let $\mathrm{EM}(\text{proof}, c)$ denote the `excessMass` at level $c$ of the uniform law on `integerBox N` relative to `A.law.siteLaw (A.physicalBox …)` built with the given proofs.
--
--   **Statement.** If $\mathrm{sliceLog}\cdot V \le p$, $\mathrm{rawCap} \le e^{p}$, $\mathrm{capLog} \le p$, and $\mathrm{EM}(\texttt{hξsource}, \texttt{hmarginSource};\ \mathrm{rawCap}) \le 6\cdot$`positiveProjectionAccuracy` $E_{\mathrm{cond}}$, then, with $c = \max(1, \mathrm{rawCap})$:
--   1. $1 \le c$ and $c \le e^{p}$;
--   2. `A.NativeDetection 0 sliceLog testLog native (forecastAugmentedUnitThreshold u p (exp (sliceLog · V)) c (exp capLog))`;
--   3. $\mathrm{EM}(\texttt{hξtarget}, \texttt{hmarginTarget};\ c) \le 6\cdot$`positiveProjectionAccuracy knob`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedRelativePositiveForecastSource_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedRelativePositiveForecastSource` (in `lean/OAI/Combinatorics/Progressions/Sampling/PreparedRelativePositiveForecastSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B308`, `OAIE3v2B277` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PreparedRelativePositiveForecastSource.lean (declaration OAI.Erdos3.VectorPolynomial.preparedRelativePositiveForecastSource)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B308
import Definitions.Def_OAIE3v2B277

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

attribute [local instance] OAI.Erdos3.VectorPolynomial.instNonemptySite
theorem preparedRelativePositiveForecastSource_s2
    (s Aexp Cdirect Cslice : ℕ) (constants : ℕ → ℕ)
    (Bstruct gainLog stageLog Plate : ℝ)
    (Pmaster : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s → ℝ)
    (hdirect : ∀ k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s,
      A.NativeDetection (preparedFiniteNestedForwardAllDegreeDegree k)
        ((preparedFiniteForwardParameter Aexp constants
          (preparedFiniteNestedForwardAllDegreeStage k).val
          (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k) + Cslice) ^ Cslice)
        ((preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
          (allocatedModelTestLog
            (preparedFiniteForwardPairedSourcePrecision Aexp Cdirect constants
              (preparedFiniteNestedForwardAllDegreeStage k).val
              (preparedFiniteNestedForwardAllDegreeIsDirect k)
              (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k) gainLog stageLog)
            (preparedFiniteForwardWork Aexp constants
              (preparedFiniteNestedForwardAllDegreeStage k).val
              (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k))))
        (preparedModularGeneralDetectorResources
          (preparedModularGeneralDetectorConstants m (preparedFiniteNestedForwardAllDegreeDegree k))
          (preparedFiniteNestedForwardAllDegreeDegree k + 1) (Pmaster k) Plate).nativeBudget
        (preparedFiniteNestedForwardFixedCenterThreshold Aexp constants Bstruct gainLog stageLog k))
    (hAexp : 2 ≤ Aexp) (hB : 0 ≤ Bstruct)
    (hgain : gainLog ∈ Set.Icc 0 Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hξsource hξtarget : ξ ≤ 1)
    (hmarginSource hmarginTarget : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (knob rawCap capLog : ℝ) :
    let seed := candidateNestedForwardSeed Aexp constants (s + 1) (2 * s + 2) Bstruct
    let u := preparedFiniteForwardModelPrecision Aexp constants (s + 1) seed gainLog stageLog
    let p := preparedFiniteForwardWork Aexp constants (s + 1) seed
    let sliceLog := (preparedFiniteForwardParameter Aexp constants (s + 1) seed + Cslice) ^ Cslice
    let testLog := (preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog
        (preparedFiniteForwardSourcePrecision Aexp constants (s + 1) seed gainLog stageLog) p)
    let native := (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) 1
      (Pmaster (preparedFiniteNestedForwardAllDegreeAnchor (2 * s + 2) (s + 1) s)) 0).nativeBudget
    let Econditional := preparedNestedFrontProjectionEnvelope Aexp constants (s + 1)
      (fun k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s => k.1.val)
      (fun k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s => k.2.1.val)
      (fun k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s =>
        (preparedModularGeneralDetectorResources
          (preparedModularGeneralDetectorConstants m (preparedFiniteNestedForwardAllDegreeDegree k))
          (preparedFiniteNestedForwardAllDegreeDegree k + 1) (Pmaster k) Plate).nativeBudget)
      Bstruct gainLog stageLog knob
    sliceLog * Fintype.card (LayerSamplerVariables G I n B) ≤ p →
    rawCap ≤ Real.exp p → capLog ≤ p →
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξsource hmarginSource)) rawCap ≤
        6 * positiveProjectionAccuracy Econditional →
    1 ≤ max 1 rawCap ∧ max 1 rawCap ≤ Real.exp p ∧
      A.NativeDetection 0 sliceLog testLog native
        (forecastAugmentedUnitThreshold u p
          (Real.exp (sliceLog * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 rawCap) (Real.exp capLog)) ∧
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξtarget hmarginTarget)) (max 1 rawCap) ≤
          6 * positiveProjectionAccuracy knob := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
