-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialSliceNativeJointGridMean_comparison
-- name    : OAI.Erdos3.VectorPolynomial.fixedSpatialSliceNativeJointGridMean_comparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T08:03:45.791575+00:00
-- url     : https://prove2.me/theorems/bbd24111-39f6-4612-bdaa-f91cb4d3a6a2
-- title:
--   The joint grid mean of the fixed spatial slice density is close to its rational reference
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$, $X$, $T$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); finite types $E_j$; $\mathbb Z$-span of `basis j` equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$ (indexed by $E_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; and a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` $W$ for reals periodCap, coverCap and $\mathrm{Lip} \in \mathbb R_{\ge 0}$ (a structure bundling a modulus, a cover, a mask and an $\mathrm{Lip}$-Lipschitz smooth part, both of norm at most $1$). Let short $=$ `allocatedShortAxis U basis S.value`, Active the non-short axes, degree $=$ `layerSamplerDegree I n`, Original $=$ `PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)`, selected $=$ `allocatedShortIntegerSelection U basis S.value`, Out $=$ `Sigma (AllocatedCongruenceRankOutput X E short)`, Joint $= X \oplus$ `AllocatedActiveIntegerAxis U basis S.value`, and Cont $= \Sigma_j I_j$.
--
--   Let $e : G \simeq X \oplus (X \oplus T)$, reals rootBudget and rootLength, and $z : \mathrm{Option}\,G \times X \to \mathbb R$ such that `fixedSpatialKernelBlock e rootBudget rootLength z b` has nonzero determinant for $b = \mathrm{false}$ (h0) and $b = \mathrm{true}$ (h1). Let $\mathrm{lowerG}, \mathrm{widthG} : G \to \mathbb R$ with $\mathrm{widthG}(g) \ne 0$, $\mathrm{lowerG}(g) \ge 0$, $\mathrm{widthG}(g) \ge 0$ and $\mathrm{lowerG}(g) + \mathrm{widthG}(g) \le 1$ for all $g$; assume $|B_a| \ge 4$ for every active $a$ (hB); let $\mathrm{lowerP}, \mathrm{widthP}$ assign reals to each active $a$ and $p \in B_a \times \mathrm{Fin}(\mathrm{degree}(a))$, and $\delta_P > 0$ with $\delta_P \le \mathrm{widthP}(a,p)$, $\mathrm{lowerP}(a,p) \ge 0$ and $|\mathrm{lowerP}(a,p)| + |\mathrm{widthP}(a,p)| \le 1$ for all $a, p$; assume $\mathrm{rootBudget} \ge 0$, $\mathrm{rootLength} \ge 0$, $|G|\cdot\mathrm{rootLength} \le \mathrm{rootBudget}$ and $|z(a)| \le 1$ for all $a$. Let sample be in `CoefficientSamplerArrays I n` over `LayerSamplerVariables G I n B`, `mixedArraySupported` for `allocatedLayerCenters`, `allocatedLayerWidths` and `allocatedLayerIntegerPMFs B U basis hR hσ S` in every layer $j$ (hs). Assume $0 < m$. Let $\tau$ be real, $\mathrm{base} : X \to \mathbb Z$, $\mathrm{box} : X \to \mathbb N$, $\mathrm{xref} : G \to$ `IntegerScalarCubeBox Empty S.value`; a finite type $\Omega$, finite probability weights law on Original, finite probability weights $\mathrm{active}(y)$ on $\Omega$ for $y \in$ Original and $Y : \mathrm{Original} \to \Omega \to \mathrm{Out} \to \mathbb Z$; natural numbers $N, q \ne 0$ with $q \mid N$, $W.\mathrm{modulus} \mid q$ and $W.\mathrm{cover} \mid q$; a real $\mathrm{gridVolume} \ne 0$; $\mathrm{center}, \mathrm{scale} : \mathrm{Joint} \to \mathbb R$ with $\mathrm{scale} > 0$; $\mathrm{cutoff} \in \mathbb N$ with $\mathrm{cutoff} > 0$; and reals $D, P, \delta$ with $D \ge 0$, $|\mathrm{Out}| + 2 \le P$, $0 \le \delta \le 1$, $q\cdot\mathrm{cutoff}/\mathrm{scale}(j) \le \delta$ for all $j$, and the decay bound: for every $i \in$ Original and every additive character $\chi$ of $(\mathrm{Out} \to \mathbb Z/N)$, $\|\texttt{finiteImageCharacteristic (active i) (Y i mod N)}\ \chi\| \le D\cdot(\mathrm{orderOf}\,\chi)^{-P}$ (the mean of $\chi(Y_i \bmod N)$ under $\mathrm{active}(i)$).
--
--   Put frame $=$ `fixedSpatialKernelSliceFrame rootBudget rootLength z lowerG widthG`; density $=$ `fixedSpatialKernelSliceOriginalForecastDensity B U basis S e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB lowerP widthP sample` (a real function on the physical-and-active domain); $C =$ `fixedSpatialOriginalForecastCap B` and $L =$ `fixedSpatialOriginalForecastLip B` (constants in $\mathbb R_{\ge 0}$ built from the kernel block equivalences of frame at false and true and from $\delta_P$); $K = \mathrm{Lip}\cdot\max(|\tau/8|,$ `forecastNativeAmbientLip U basis o R`$)$; $c_a = (\mathrm{sample}_{j})_2(i)$ for $\langle j, i\rangle = \mathrm{selected}(a)$; grid $=$ `forecastInactiveFixedOutput B U basis S selected c xref`; and test $=$ `W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover (a ↦ base a / box a) τ`. Then
--   $$\Bigl\|\texttt{forecastJointOriginalGridMean U basis S.value hm law active grid Y N q hq gridVolume density test center scale} - \sum_g \mathop{\mathbb E}_{r : \mathrm{Out} \to \mathbb Z/N}\frac{\texttt{rationalInactiveForecast law active grid Y N gridVolume g r}}{\mathrm{gridVolume}}\int \mathrm{test}(g, r \bmod q, y)\,d\mu(y)\Bigr\|$$
--   $$\le \Bigl(\mathrm{cutoff}^{|\mathrm{Out}|+1}\cdot 2\cdot 8^{|\mathrm{Joint}|}(L + CK)\delta + \frac{D}{\mathrm{cutoff}}\cdot 8^{|\mathrm{Joint}|}L\delta\Bigr)6^{|\mathrm{Cont}|} + 2\frac{D}{\mathrm{cutoff}},$$
--   where $\sum_g$ is a `tsum` over grids, $r \bmod q$ is the image under the ring map $\mathbb Z/N \to \mathbb Z/q$, and $\mu$ is Lebesgue measure with density $\max(\mathrm{density}, 0)$ (`realDensityMeasure volume density`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.fixedSpatialSliceNativeJointGridMean_comparison` in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedFixedPathRecoveredJointGridComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B167`, `OAIErdos3B185` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedFixedPathRecoveredJointGridComparison.lean#L646

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B167
import Definitions.Def_OAIErdos3B185

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical
variable {X : Type*} {m : ℕ} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L

variable [Fintype X] [∀ j, Fintype (E j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis L hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis L

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

variable [NeZero q]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Joint" => X ⊕ AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Joint" => X ⊕ AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)

include hR hσ in
theorem fixedSpatialSliceNativeJointGridMean_comparison
    (e : G ≃ X ⊕ (X ⊕ T)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
    (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
    (lowerG widthG : G → ℝ) (hwGne : ∀ g, widthG g ≠ 0)
    (hlG : ∀ g, 0 ≤ lowerG g) (hwG : ∀ g, 0 ≤ widthG g)
    (hcontainedG : ∀ g, lowerG g + widthG g ≤ 1)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lowerP widthP : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {δP : ℝ} (hδP : 0 < δP)
    (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget)
    (hz : ∀ a, |z a| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hm : 0 < m)
    (τ : ℝ) (base : X → ℤ) (box : X → ℕ)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Original)
    (active : Original → FiniteProbabilityWeights Ω)
    (Y : Original → Ω → Out → ℤ)
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q ∣ N)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (gridVolume : ℝ) (hV : gridVolume ≠ 0)
    (center scale : Joint → ℝ) (hscale : ∀ j, 0 < scale j)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ) :
    let frame := fixedSpatialKernelSliceFrame rootBudget rootLength z lowerG widthG
    let h0slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG false h0 hwGne
    let h1slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG true h1 hwGne
    let density := fixedSpatialKernelSliceOriginalForecastDensity B U basis S e rootBudget rootLength z
      lowerG widthG h0 h1 hwGne hB lowerP widthP sample
    let C := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let L := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame false h0slice)
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let K := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let grid := forecastInactiveFixedOutput B U basis S selected c xref
    let test := W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
    ‖forecastJointOriginalGridMean U basis S.value hm law active grid Y N q hq
        gridVolume density test center scale -
      (∑' g, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast law active grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
          ∫ y, test g (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * 8 ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * (8 ^ Fintype.card Joint * (L : ℝ) * δ)) *
          6 ^ Fintype.card Cont + 2 * (D / cutoff) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
