-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_recovered_native_atom_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_atom_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:07:26.802957+00:00
-- url     : https://prove2.me/theorems/0e86aac2-b9f1-4829-8ca9-08233434a25d
-- title:
--   The forecast short-grid test at a sliced fixed-path point equals the native normalized twist evaluation
-- statement:
--   **Setup.** Fix the data of OpenAI's allocated layer-sampler setup: a natural number $m > 0$ (hypothesis $hm$); finite types $G$, $X$, $I_j$, $J_j$, $E_j$ ($j < m$) and $B(a)$ for each layer-sampler axis $a$; dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases `basis j` (indexed by $\{0,\dots,n_j-1\}$) of the orthogonal complement of $U_j$ with $hb$: the $\mathbb{Z}$-span of `basis j` is `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ (indexed by $I_j$) of $U_j$; $\mathbb{Z}$-bases $bW_j$ (indexed by $E_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; reals $R_j > 0$, $\sigma_j > 0$; and a `LayerSamplerScale B U basis R σ` $S$ with positive integer side `S.value`. Write `short` = `allocatedShortAxis U basis S.value`, call the other axes active, let $\mathrm{Input}$ be the set of triples (active axis $a$, element of $B(a)$, index below `layerSamplerDegree I n a`), $\mathrm{Output}$ the set of active axes, $\mathrm{ShortTuple}$ = `PrincipalAxisTuples (α := Empty) short (allocatedPrincipalSides B U basis S)`, and `selected` = `allocatedShortIntegerSelection U basis S.value`.
--
--   Let $W$ be a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` (an OpenAI structure, with a period `W.modulus` and a cover `W.cover`). Let `sample` be a `CoefficientSamplerArrays` for the variables `LayerSamplerVariables G I n B`, assumed ($hs$) for every $j$ to be supported (`mixedArraySupported`) on the centers, widths and integer PMFs `allocatedLayerCenters`, `allocatedLayerWidths`, `allocatedLayerIntegerPMFs` of layer $j$. Let $\mathrm{base} : X \to \mathbb{Z}$, `integerFrame` an integer function on $\texttt{Option}(\text{variables}) \times X$, $\mathrm{box} : X \to \mathbb{N}$ with ($hbox$) $\mathrm{box}(a) > 0$, $\tau$ a real with ($h\tau$) $\tau \ne 0$, and $q \ge 1$ a natural number with ($hperiod$) `W.modulus` dividing $q$ and ($hcover$) `W.cover` dividing $q$. For each $j$ let $\mathrm{nativePoly}_j$ be a `VectorPolynomial X ℝ (J j → ℝ)` with ($hmem$) all coefficients in $U_j$ and ($hdegree$) degree at most $j+1$ (unit weights). Assume:
--   - ($hbase$) `canonicalCoefficientSample U basis hb o sample` equals `affineSampleCoefficientTorus U nativePoly hmem` evaluated at the real point $(k, x) \mapsto (\texttt{integerBaseTranslation base} + \texttt{integerFrame})(k, x)$;
--   - ($hsmallChart$) $\lvert \texttt{coefficientSamplerAmbientPoint U basis o sample}\ a\rvert < 1/2$ for every $a$;
--   - ($hread$) `read` is an integer function on `AllocatedActualCoefficientIndex G X I E n B` such that for every event (predicate) on `CoefficientChartResidues … W.cover`, `coefficientDeckChartEvent U bW basis hb o W.cover event` holds at `affineCoefficientCoverSample U nativePoly hmem W.cover` (of the same real point) if and only if the event holds at `allocatedReadCoefficientChartResidues` of the residues of `read` modulo `W.cover`.
--
--   (The hypotheses $hs$, $hbox$, $h\tau$, $hdegree$, $hbase$, $hsmallChart$, $hread$ are included in the statement.)
--
--   **Statement.** Let $H_G : G \to \mathbb{N}$ be positive, $c_G : G \to \mathbb{Z}$, $\mathrm{step}_G \in \mathbb{N}$, with each progression `integerProgressionSupport (cG g) stepG (HG g)` contained in $[0, \texttt{S.value})$. Let $\mathrm{step}, H : \mathrm{Input} \to \mathbb{N}$ and $c : \mathrm{Input} \to \mathbb{Z}$ with $H > 0$ and each progression `integerProgressionSupport (c j) (step j) (H j)` contained in $[0, \texttt{S.value})$. Let $u \in \mathrm{ShortTuple}$; let $x = (x_g)$ with $x_g \in$ `IntegerScalarCubeBox Empty (HG g)` have nonzero weight under the product of the laws `integerScalarCubeWeights Empty (HG g)`; and let $v = (v_j)$ with $v_j \in$ `IntegerScalarCubeBox Empty (H j)` have nonzero weight under the product of the laws `integerScalarCubeWeights Empty (H j)`. Put `embed g` = `containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) (x g)` and `joined` = `principalAxisJoin short u (allocatedActiveContainedProgression B U basis S step H c hsubset v)`, and let $\mathrm{root}$ = `allocatedPhysicalCubeRoot B U basis S 0 embed joined`. Then
--   $$\texttt{W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover}\ (a \mapsto \mathrm{base}(a)/\mathrm{box}(a))\ \tau\ \Gamma\ \Theta\ (\Phi, \Psi)$$
--   equals
--   $$\texttt{W.eval box nativePoly}\bigl(a \mapsto \mathrm{base}(a) + \texttt{integerPhysicalSite}(\mathrm{root}, \texttt{integerFrame}, a)\bigr),$$
--   where
--   - $\Gamma$ = `forecastInactiveShortGrid B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) u`;
--   - $\Theta$ = `allocatedJointResidueOutput B U basis S base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample) q` applied to the residues $g \mapsto (c_G(g) + \mathrm{step}_G \cdot x_g) \bmod q$ and to `allocatedPrincipalResidueJoin B U basis S q u` of the residues $j \mapsto (c(j) + \mathrm{step}(j)\cdot v_j) \bmod q$ (where $x_g$ and $v_j$ denote the coordinate of the one-point cube);
--   - $\Phi$ sends $(a, \cdot)$, for $a \in X$, to $\texttt{integerPhysicalSite}(\mathrm{root}, \texttt{integerFrame}, a) / (\tau\, \mathrm{box}(a)/8)$;
--   - $\Psi$ sends an active axis $a \in \mathrm{Output}$ to `allocatedFullMixedSiteValue U basis (allocatedOriginalSamplePhysicalMixedValue B U basis S sample embed joined) a`.
--
--   All named functions are defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_atom_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_atom` (in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathAnchoredNativeComparison.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B232`, `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathAnchoredNativeComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_atom)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B232
import Definitions.Def_OAIE3v2B236

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedNativeAtomCoverNeZero
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (hbox : ∀ a, 0 < box a) {τ : ℝ} (hτ : τ ≠ 0)
variable (q : ℕ) [NeZero q] (hm : 0 < m)
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

include hs hbox hτ hdegree hbase hsmallChart hread in

theorem allocatedFixedPath_sliced_recovered_native_atom_s2
    (HG : G → ℕ) (hHG : ∀ g, 0 < HG g) (cG : G → ℤ) (stepG : ℕ)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (u : ShortTuple)
    (x : ∀ g, IntegerScalarCubeBox Empty (HG g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (HG g) (hHG g))).weight x ≠ 0)
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0) :
    let embed := fun g => containedProgressionCubeMap Empty S.value (HG g) stepG (cG g)
      S.positive (hcontainedG g) (x g)
    let joined := principalAxisJoin short u (allocatedActiveContainedProgression B U basis S step H c hsubset v)
    W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
      (forecastInactiveShortGrid B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) u)
      (allocatedJointResidueOutput B U basis S base integerFrame (allocatedReadDeck read)
        (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
        (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
        (allocatedPrincipalResidueJoin B U basis S q u
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))))
      ((fun a : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) embed joined)
            integerFrame a.1 : ℝ) / (τ * (box a.1 : ℝ) / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U basis
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample embed joined) a.1.val) =
      W.eval box nativePoly (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) embed joined) integerFrame a) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
