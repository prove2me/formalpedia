-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_stepInputLaw_sample_characteristic_decay_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.stepInputLaw_sample_characteristic_decay_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:56:56.280208+00:00
-- url     : https://prove2.me/theorems/b4a040a5-fe81-41f9-9330-f90774fd13a3
-- title:
--   Characters of the sampled forecast polynomial decay under the step input law
-- statement:
--   Work in OpenAI's layer-sampler setting, with the following implicit: a natural number $m$; finite types $G$, $I_j$, $J_j$, $B_a$ and natural numbers $n_j$; subspaces $U_j\subseteq\mathbb{R}^{J_j}$ and bases $b_j$ of the orthogonal complements of `euclideanSubspace (U j)`; reals $R_j>0$, $\sigma_j>0$ (proofs $hR$, $h\sigma$) and a `LayerSamplerScale` $S$; a finite type $X$ with decidable equality; finite types $E^{\mathrm{out}}_j$; natural numbers $D_{\mathrm{mod}},L_{\mathrm{rank}}$; embeddings $\mathrm{spatial}$, $\mathrm{kernel}_j$, $\mathrm{block}_{j,a}$; a type $T_{\mathrm{sp}}$ and an equivalence $G\simeq X\oplus(X\oplus T_{\mathrm{sp}})$; reals $W_{\mathrm{sp}},L_{\mathrm{sp}}$; $\mathrm{physicalN}:X\to\mathbb{N}$; and reals $\tau,\delta_{\mathrm{slice}},P,P_{\mathrm{bad}},P_{\mathrm{pres}}$. Let $\mathrm{slice}$ be an `ActualFixedSpatialSlicedForecastPath` for this data (a structure bundling an `ActualFixedSpatialForecastPath` $\mathrm{slice.path}$, with its primes, exponents, prescribed valuations, base, noise, read-out, coefficient sample and natural number $R_{\mathrm{bad}}$, together with step and progression data), and write $Q$ for `slice.path.referenceModulus` ($\prod_{p}p^{\mathrm{exponent}(p)}$ over the path's primes). Assume $m>0$. Let $y$ be an element of `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)` and $\chi$ an additive character, with values in $\mathbb{C}$, of the group of maps from `Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis U b S.value))` to $\mathbb{Z}/Q$. Let $\Phi(t)$ be the map $j\mapsto$ (residue mod $Q$ of the evaluation of the $j$-th polynomial of `allocatedForecastPolynomial (allocatedShortAxis U b S.value) slice.path.base slice.path.noise (allocatedReadDeck slice.path.read) (allocatedOriginalSampleCongruenceProjection B U b S slice.path.sample)` at the long variables $t$, lifted to integers, and the inactive variables $y$), as in `integerLongPolynomialOutput`. Then, with $\kappa$ = `modularRankDecayExponent m (modularForecastRankConstant m Dmod)` and $c$ = `modularRankChargeFactor m` ($=4m\cdot2^m m!$),
--   $$\big|\mathbb{E}_{t\sim\mathrm{slice.stepInputLaw}}\,\chi(\Phi(t))\big|\ \le\ \Big(R_{\mathrm{bad}}\prod_{p}p^{\mathrm{prescribed}(p)}\Big)^{\kappa c}\,\mathrm{orderOf}(\chi)^{-\kappa},$$
--   the left side being `finiteImageCharacteristic slice.stepInputLaw Φ χ`, the product over the path's primes, and $R_{\mathrm{bad}}$, $\mathrm{prescribed}$ those of $\mathrm{slice.path}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.stepInputLaw_sample_characteristic_decay_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.stepInputLaw_sample_characteristic_decay` (in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B252` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.stepInputLaw_sample_characteristic_decay)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252

section

namespace OAI

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

local instance slicedDecayModulusNeZero_r870b21_1 : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩
omit [Fintype Tsp] in

theorem stepInputLaw_sample_characteristic_decay_s2 (hm : 0 < m)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod slice.path.referenceModulus) ℂ) :
    ‖finiteImageCharacteristic slice.stepInputLaw
      (fun t j => (integerLongPolynomialOutput
        (allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
          slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
          (allocatedOriginalSampleCongruenceProjection B U b S slice.path.sample))
        (fun k => (y k.1 k.2 : ℤ)) slice.path.referenceModulus t j :
          ZMod slice.path.referenceModulus)) χ‖ ≤
      ((slice.path.Rbad * ∏ p : slice.path.primes,
        p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
          modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m
          (modularForecastRankConstant m Dmod : ℝ)) := by
  sorry

end ActualFixedSpatialSlicedForecastPath

end Erdos3.VectorPolynomial

end

end OAI
end
