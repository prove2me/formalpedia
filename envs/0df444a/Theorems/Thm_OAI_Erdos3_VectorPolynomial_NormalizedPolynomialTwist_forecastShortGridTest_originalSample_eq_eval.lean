-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_NormalizedPolynomialTwist_forecastShortGridTest_originalSample_eq_eval
-- name    : OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.forecastShortGridTest_originalSample_eq_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T02:43:21.856913+00:00
-- url     : https://prove2.me/theorems/adca134c-15e7-4aa7-9d10-e6afbdc79422
-- title:
--   The forecast short-grid test at an original sample equals the twist evaluation
-- statement:
--   Fix $m \in \mathbb N$, a finite type $X$, finite types $I_j$ and $E_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)` such that ($h_b$) the $\mathbb Z$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`, orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$, $\mathbb Z$-bases $bW_j$ indexed by $E_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the integer lattice intersected with that subspace), and reals $R_j > 0$. Let $G$ be a finite type, $B_a$ finite types indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), $\sigma_j > 0$ reals, and $S$ a `LayerSamplerScale` for $(B, U, b, R, \sigma)$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let sample be in `CoefficientSamplerArrays I n` over the variables `LayerSamplerVariables G I n B` (for each $j$, a real array on $I_j$ and an integer array on $\mathrm{Fin}(n_j)$, indexed by bounded exponents) and assume, for every $j$, `mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)` (the sample lies where OpenAI's mixed coefficient density is nonzero). Let $x : G \to$ `IntegerScalarCubeBox Empty S.value` and $v \in$ `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)`; write $\mu_j =$ `allocatedOriginalSamplePhysicalMixedValue B U b S sample x v j` $\in \mathbb R^{I_j} \times \mathbb Z^{\mathrm{Fin}(n_j)}$ and short for the predicate `allocatedShortAxis U b S.value` on `LayerSamplerAxis I n`. Let $W$ be a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` (a structure bundling a positive modulus, a positive cover, a mask on $(\mathbb Z/\mathrm{modulus})^X$ and a Lipschitz smooth function, both bounded by 1). Let $q \ne 0$ be a natural number, assume $0 < m$, $W.\mathrm{modulus} \mid q$ and $W.\mathrm{cover} \mid q$; let $\mathrm{base}, u : X \to \mathbb Z$, $N : X \to \mathbb N$ with $N > 0$ pointwise, $\tau \ne 0$ real, $\mathrm{deck}_j \in \mathbb Z^{E_j}$, and $\mathrm{poly}_j$ vector polynomials in variables $X$ over $\mathbb R$ with values in $\mathbb R^{J_j}$ all of whose coefficients lie in $U_j$ ($h_{\mathrm{mem}}$). Assume that for every $j$, `BooleanCubeKernel.physicalSingleSiteValue U W.cover poly hmem u j ()` equals `normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) W.cover (orthonormalMixedChart (o j) μ_j, deck_j mod W.cover)`. Then `W.forecastShortGridTest U b S.value hb o bW R q hm hperiod hcover`, with center $z \mapsto \mathrm{base}(z)/N(z)$, the given $\tau$, the grid `forecastInactiveShortGrid B U b S (allocatedShortIntegerSelection U b S.value) (allocatedOriginalSampleInactiveCoefficients B (allocatedShortIntegerSelection U b S.value) sample) (principalAxisRestrict short v)`, and the output labels `forecastCongruenceOutput short u (j ↦ Sum.elim (μ_j).2 deck_j)` reduced mod $q$, evaluated at the point whose first component is $a \mapsto (u(a_1) - \mathrm{base}(a_1))/(\tau N(a_1)/8)$ and whose second component sends each axis $a$ with $\neg\,\mathrm{short}\,a$ to `allocatedFullMixedSiteValue U b μ a` (with $R$), equals `W.eval N poly u` $=$ `W.mask` $(u \bmod W.\mathrm{modulus}) \cdot$ `W.smooth` $(u/N,$ `physicalGridFactorInput W.cover poly u`$)$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.forecastShortGridTest_originalSample_eq_eval` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastNativeJointTestBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B167`, `OAIErdos3B173` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastNativeJointTestBudget.lean#L438

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B167
import Definitions.Def_OAIErdos3B173

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Grid" => AllocatedShortIntegerAxis U b Lsize →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

end NormalizedPolynomialTwist

section OriginalSample
variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
  (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (v : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S))

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

include hR hσ hs in
theorem forecastShortGridTest_originalSample_eq_eval
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (base u : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ : ℝ} (hτ : τ ≠ 0) (deck : ∀ j, E j → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (poly j) a ∈ U j)
    (hchart : let _ : NeZero W.cover := ⟨W.cover_pos.ne'⟩
      ∀ j, BooleanCubeKernel.physicalSingleSiteValue U W.cover poly hmem (fun x => (u x : ℝ)) j () =
        normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) W.cover
          (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v j),
            integerResidueMap (E j) W.cover (deck j))) :
    W.forecastShortGridTest U b S.value hb o bW R q hm hperiod hcover
      (fun z => (base z : ℝ) / N z) τ
      (forecastInactiveShortGrid B U b S (allocatedShortIntegerSelection U b S.value)
        (allocatedOriginalSampleInactiveCoefficients B (allocatedShortIntegerSelection U b S.value) sample)
        (principalAxisRestrict (allocatedShortAxis U b S.value) v))
      (fun a => (forecastCongruenceOutput (R := ℤ) (allocatedShortAxis (I := I) U b S.value) u
        (fun j => Sum.elim (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v j).2
          (deck j)) a : ZMod q))
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)),
        fun a : (Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) =>
          allocatedFullMixedSiteValue (R := R) U b
            (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v) a.1.val) =
      W.eval N poly u := by
  sorry

end NormalizedPolynomialTwist
end OriginalSample
end Erdos3.VectorPolynomial
end
end OAI
