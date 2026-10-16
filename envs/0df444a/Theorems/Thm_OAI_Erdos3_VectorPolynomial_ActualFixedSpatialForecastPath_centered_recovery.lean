-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_centered_recovery
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.centered_recovery
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T02:13:23.39309+00:00
-- url     : https://prove2.me/theorems/1d1c070f-7ed4-46f5-8acf-864c9a6b6cd8
-- title:
--   A centered recovered sample read along an actual forecast path recovers its coefficients
-- statement:
--   Fix the data of OpenAI's actual fixed-spatial forecast setting: a natural number $m$; a finite type $G$; finite types $I_j$ ($j \in \mathrm{Fin}\,m$) and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$ for all $j$; a finite type $X$ with decidable equality; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis (allocatedShortAxis U b S.value) j`; the predicate `allocatedShortAxis U b S.value` holds exactly of the axes $\langle j, \mathrm{inr}\ i\rangle$ with `basisAxisScale (b j) i` $\le S.\mathrm{value}^{j+1}$); a finite type $T$ and an equivalence $G \simeq X \oplus (X \oplus T)$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); and reals $\tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$. Let `path` be an `ActualFixedSpatialForecastPath` over these data (a structure bundling a base point `path.base` $: X \to \mathbb Z$, a noise vector `path.noise` $: \mathrm{Option}(\mathrm{Vars}) \times X \to \mathbb Z$ with $\mathrm{Vars} =$ `LayerSamplerVariables G I n B`, sample arrays `path.sample : CoefficientSamplerArrays I n`, an integer read-off `path.read` on `AllocatedActualCoefficientIndex G X I E n B`, centers `path.center j` $\in U_j$, primes, exponents and further data with bounds).
--
--   Let $bW_j$ be a $\mathbb Z$-basis, indexed by $E_j$, of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; let $hb$ say that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$; let $\mathrm{originalpoly}_j$ be vector polynomials on $X$ with values in $\mathbb R^{J_j}$ all of whose coefficients lie in $U_j$ (hypothesis $hmem$); let $C$ be real; let `center` be a point of the `CoefficientTorus U` (a quotient of a coefficient array space by an integer lattice); and let `sampleFn` and `readFn` be functions of the noise $z : \mathrm{Option}(\mathrm{Vars}) \times X \to \mathbb Z$ giving sample arrays and integer read-offs. Assume
--
--   1. `AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem (allocatedShortAxis U b S.value) spatial kernel block C center path.center path.base sampleFn readFn` (a proposition of OpenAI saying that for every noise $z$ the read-off recovers $z$ and, whenever the centered joint density at $z$ is nonzero, the sample and read-off at $z$ satisfy a list of recovery identities and bounds);
--   2. `allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem center path.base path.noise` $\ne 0$;
--   3. `sampleFn path.noise = path.sample` and `readFn path.noise = path.read`.
--
--   Then: (a) `canonicalCoefficientSample U b hb o path.sample` equals `affineSampleCoefficientTorus U (path.physicalPolynomial originalpoly) _ F`, where `path.physicalPolynomial originalpoly` is $j \mapsto \mathrm{originalpoly}_j$ minus the constant `path.center j` and $F(k, x)$ is the real cast of `jointIntegerFrame (path.base, path.noise) k x`; (b) for every $j$, `mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (path.sample j)` and `mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (path.sample j)`; (c) $|$`coefficientSamplerAmbientPoint U b o path.sample d`$| < 1/2$ for every index $d$; (d) for every natural number $q > 0$ and every predicate `event` on `CoefficientChartResidues Vars n E q`, `coefficientDeckChartEvent U bW b hb o q event` holds at `affineCoefficientCoverSample U (path.physicalPolynomial originalpoly) _ q F` if and only if `event` holds at `allocatedReadCoefficientChartResidues` of the read-off `path.read` reduced mod $q$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.centered_recovery` in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1330` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean#L51

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1330

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}

omit [Fintype Tsp] in
theorem centered_recovery
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem
      (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
      center path.center path.base sampleFn readFn)
    (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
      center path.base path.noise ≠ 0)
    (hsample : sampleFn path.noise = path.sample)
    (hread : readFn path.noise = path.read) :
    canonicalCoefficientSample U b hb o path.sample =
      affineSampleCoefficientTorus U (path.physicalPolynomial originalpoly)
        (path.physicalPolynomial_mem originalpoly hmem)
        (fun k x => (jointIntegerFrame (path.base, path.noise) k x : ℝ)) ∧
    (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (path.sample j) ∧
      mixedArraySupported (allocatedLayerCenters B U b S j)
        (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)
        (path.sample j)) ∧
    (∀ d, |coefficientSamplerAmbientPoint U b o path.sample d| < 1 / 2) ∧
    (∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
      ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n Eout q → Prop,
        coefficientDeckChartEvent U bW b hb o q event
          (affineCoefficientCoverSample U (path.physicalPolynomial originalpoly)
            (path.physicalPolynomial_mem originalpoly hmem) q
            (fun k x => (jointIntegerFrame (path.base, path.noise) k x : ℝ))) ↔
          event (allocatedReadCoefficientChartResidues (fun i => (path.read i : ZMod q)))) := by
  sorry

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial
end
end OAI
