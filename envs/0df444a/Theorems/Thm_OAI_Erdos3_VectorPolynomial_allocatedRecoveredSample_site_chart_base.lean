-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRecoveredSample_site_chart_base
-- name    : OAI.Erdos3.VectorPolynomial.allocatedRecoveredSample_site_chart_base
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:48:15.411918+00:00
-- url     : https://prove2.me/theorems/73c931ef-148c-4b34-831e-826ce13bb42e
-- title:
--   The physical single-site value of a recovered sample equals its covered chart point
-- statement:
--   Fix $m \in \mathbb N$, a type $X$, finite types $J_j$ ($j \in \mathrm{Fin}\,m$) with subspaces $U_j \le \mathbb R^{J_j}$, a finite type $G$, finite types $I_j$ and $E_j$, $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), $\mathbb Z$-bases $bW_j$ indexed by $E_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the integer lattice intersected with that subspace), bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)` such that ($h_b$) the $\mathbb Z$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`, orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Write $\mathcal V$ for `LayerSamplerVariables G I n B`. Let $q \ne 0$ be a natural number; let $\mathrm{poly}_j$ be vector polynomials in variables $X$ over $\mathbb R$ with values in $\mathbb R^{J_j}$, of degree at most $j+1$ (`DegreeLE 1 (j+1)`: every coefficient of total degree $> j+1$ vanishes), all of whose coefficients lie in $U_j$ ($h_m$); let $\mathrm{base} : X \to \mathbb Z$, $\mathrm{noise} : \mathrm{Option}\,\mathcal V \times X \to \mathbb Z$, and sample in `CoefficientSamplerArrays I n` over $\mathcal V$, and write $w = $ `integerBaseTranslation base` $+ \mathrm{noise}$ (an integer array on $\mathrm{Option}\,\mathcal V \times X$; `integerBaseTranslation base` places base in the none row and $0$ elsewhere). Assume `canonicalCoefficientSample U b hb o sample` $=$ `affineSampleCoefficientTorus U poly hm w` (as points of the coefficient torus, with $w$ cast to reals), and $|$`coefficientSamplerAmbientPoint U b o sample a`$| < 1/2$ for every $a$. Let $\mathrm{read} :$ `AllocatedActualCoefficientIndex G X I E n B` $\to \mathbb Z$ be such that for every predicate event on `CoefficientChartResidues 𝒱 n E q`, `coefficientDeckChartEvent U bW b hb o q event (affineCoefficientCoverSample U poly hm q w)` holds if and only if event holds of `allocatedReadCoefficientChartResidues (read mod q)`. Then for every $x : G \to$ `IntegerScalarCubeBox Empty S.value`, every $y \in$ `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)` and every $j \in \mathrm{Fin}\,m$,
--   `physicalSingleSiteValue U q poly hm (z ↦ base z + integerPhysicalSite root noise z) j ()`
--   equals
--   `normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) q (orthonormalMixedChart (o j) μ_j, integerResidueMap (E j) q (allocatedOriginalSampleDeckValue B U b S (allocatedReadDeck read) x y j))`,
--   where $\mathrm{root} =$ `allocatedPhysicalCubeRoot B U b S 0 x y`, `integerPhysicalSite root noise` is $z \mapsto \mathrm{noise}(\mathrm{none}, z) + \sum_k \mathrm{root}(k)\,\mathrm{noise}(\mathrm{some}\,k, z)$, $\mu_j =$ `allocatedOriginalSamplePhysicalMixedValue B U b S sample x y j`, and `integerResidueMap` reduces an integer vector mod $q$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedRecoveredSample_site_chart_base` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedRecoveredSampleSiteChart.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B147`, `OAIErdos3B161`, `OAIErdos3B173` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedRecoveredSampleSiteChart.lean#L113

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B147
import Definitions.Def_OAIErdos3B161
import Definitions.Def_OAIErdos3B173

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators Matrix

variable {K X : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

section Allocated
variable {G : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedRecoveredSample_site_chart_base
    (q : ℕ) [NeZero q]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hbase : canonicalCoefficientSample U b hb o sample =
      affineSampleCoefficientTorus U poly hm (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base + noise) (k,x) : ℝ)))
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o sample a| < 1/2)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
      coefficientDeckChartEvent U bW b hb o q event
        (affineCoefficientCoverSample U poly hm q (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base + noise) (k,x) : ℝ))) ↔
      event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q))))
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (j : Fin m) :
    physicalSingleSiteValue U q poly hm
      (fun z => (base z + integerPhysicalSite (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) noise z : ℝ)) j () =
      normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) q
        (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U b S sample x y j),
          integerResidueMap (E j) q
            (allocatedOriginalSampleDeckValue B U b S (allocatedReadDeck read) x y j)) := by
  sorry

end Allocated
end Erdos3.VectorPolynomial
end
end OAI
