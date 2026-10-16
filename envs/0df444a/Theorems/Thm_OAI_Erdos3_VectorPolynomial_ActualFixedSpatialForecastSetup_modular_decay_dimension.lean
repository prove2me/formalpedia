-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastSetup_modular_decay_dimension
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.modular_decay_dimension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:22:12.327044+00:00
-- url     : https://prove2.me/theorems/ee3bfa9c-7c97-4ff3-803e-6e4e28042a18
-- title:
--   An actual forecast setup bounds the congruence output dimension by the decay exponent
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j \in \mathrm{Fin}\,m$) finite types, $n : \mathrm{Fin}\,m \to \mathbb N$, and $B_a$ finite types for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); let $J_j$ be finite types, $U_j \le \mathbb R^{J_j}$ real subspaces and $b_j$ bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb R$ and $S$ a `LayerSamplerScale` for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); let $X$ be a finite type, $E_j$ finite types (`Eout`), $D_{\mathrm{mod}}$ a natural number, $\tau, \delta_{\mathrm{slice}}$ reals, $A$ a type and $\mathrm{selected} : A \to \Sigma_j\, \mathrm{Fin}(n_j)$. Suppose there is an `ActualFixedSpatialForecastSetup B U b S Dmod selected τ δslice` (over $X$ and $E$; a structure bundling the inequalities $0 < m$, $|X| + \sum_j (|E_j| + n_j) \le D_{\mathrm{mod}}$, injectivity of $\mathrm{selected}$, and many real parameters with bounds). Then
--   $$\Bigl|\Sigma_j\, \mathrm{AllocatedCongruenceRankOutput}(X, E, \mathrm{short}, j)\Bigr| + 2 \le \mathrm{modularRankDecayExponent}\bigl(m,\ \mathrm{modularForecastRankConstant}(m, D_{\mathrm{mod}})\bigr),$$
--   where $\mathrm{short}$ is the predicate `allocatedShortAxis U b S.value` on axes (true exactly of the axes $\langle j, \mathrm{inr}\ i\rangle$ with `basisAxisScale (b j) i` $\le S.\mathrm{value}^{j+1}$), `AllocatedCongruenceRankOutput X E short j` is the type `SpatialDegreeOutput X j` $\oplus (E_j \oplus$ `AllocatedCongruenceIntegerAxis short j`$)$, `modularForecastRankConstant s D` $= (D+2)(2^s s!)\,2^s$ and `modularRankDecayExponent s C` $= C/(2^s s!)/2^s$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.modular_decay_dimension` in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1330` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean#L153

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

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

end ActualFixedSpatialSlicedForecastPath

namespace ActualFixedSpatialForecastSetup
variable {B U b S Dmod τ δslice}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

omit [DecidableEq X] [Fintype A] in
include s in
theorem modular_decay_dimension :
    ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) := by
  sorry

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial
end
end OAI
