-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:33:20.795514+00:00
-- url     : https://prove2.me/theorems/b4e6df23-5b88-4634-b92d-bc4eb02d1fd4
-- title:
--   The retained recovered rational factor is bounded by a grid fiber-mean cap times a power of the retained CRT modulus
-- statement:
--   Fix the data of OpenAI's layered-sampler setup: natural numbers $m$, $L_{\mathrm{rank}}$, $D_{\mathrm{mod}}$, finite types $G$, $I_j$, $J_j$, $E^{\mathrm{out}}_j$ ($j < m$), $X$ (with decidable equality), $T_{\mathrm{sp}}$, $B(a)$ (for each layer-sampler axis $a$), dimensions $n_j$, subspaces $U_j \subseteq \mathbb{R}^{J_j}$, bases $b_j$ (indexed by $\{0, \dots, n_j - 1\}$) of the orthogonal complement of $U_j$, positive reals $R_j, \sigma_j$, a `LayerSamplerScale B U b R σ` $S$, embeddings `spatial`, `kernel`, `block`, an equivalence `spatialEquiv` $: G \simeq X \sqcup (X \sqcup T_{\mathrm{sp}})$, reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}, \tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$, a map $\mathrm{physicalN} : X \to \mathbb{N}$, and a structure `slice : ActualFixedSpatialSlicedForecastPath` built from all of these (all defined by OpenAI). Further let $A$ be a finite type, `selected` $: A \to \Sigma_{j < m} \{0, \dots, n_j - 1\}$, $bW_j$ a $\mathbb{Z}$-basis indexed by $E^{\mathrm{out}}_j$ of the lattice section `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, a proof $hb$ that for each $j$ the $\mathbb{Z}$-span of the vectors $b_j(i)$ equals `projectedIntegerLattice (euclideanSubspace (U j))`, a natural number $d$ with an equivalence $e : \{0, \dots, d-1\} \simeq \Sigma_j J_j$, and a natural number `cutoff`.
--
--   Write $q$ for `slice.path.referenceRetainedCRTModulus cutoff` (a positive natural number, the product over the retained primes $\ell$ of $\ell$ to its exponent), $\mathrm{vol} = \prod_{a \in A} \texttt{basisAxisScale}(b_{j_a}, i_a)$ where $\texttt{selected}(a) = (j_a, i_a)$ and `basisAxisScale b i` $= \lceil \lVert b_i \rVert^{-1} \rceil$ (natural-number ceiling), and `grid` for `forecastInactiveFixedOutput B U b S selected (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample) slice.path.commonTuple` (an OpenAI-defined integer-valued output map on the principal integer tuples). Let $I_{\mathrm{cap}}$ be a real number such that for every $z : A \to \mathbb{Z}$,
--   $$\mathrm{vol} \cdot \texttt{slice.principalLaw.fiberMean}\ \mathrm{grid}\ (a, \_ \mapsto z(a))\ (\_ \mapsto 1) \le I_{\mathrm{cap}},$$
--   that is, $\mathrm{vol}$ times the probability, under the finite probability law `slice.principalLaw`, that `grid` takes the value $(a, \_) \mapsto z(a)$, is at most $I_{\mathrm{cap}}$.
--
--   Then for every $r : X \to \mathbb{Z}/q\mathbb{Z}$ and every $\beta : \{0, \dots, d-1\} \to \mathbb{Z}$,
--   $$\bigl\lvert \texttt{slice.retainedRecoveredRationalFactor selected bW hb e cutoff r beta} \bigr\rvert \le I_{\mathrm{cap}} \cdot q^{\lvert \mathrm{Out} \rvert},$$
--   where `retainedRecoveredRationalFactor` is a real number defined by OpenAI and $\mathrm{Out}$ is the finite type $\Sigma\ \texttt{AllocatedCongruenceRankOutput X Eout (allocatedShortAxis U b S.value)}$ of congruence output coordinates.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedRecoveredRationalFactor_abs_le_grid_modulus_pow` (in `lean/OAI/Combinatorics/Progressions/Sampling/ActualFixedSpatialSlicedRetainedKernelGridCap.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B303` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualFixedSpatialSlicedRetainedKernelGridCap.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedRecoveredRationalFactor_abs_le_grid_modulus_pow)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B303

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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout
  (allocatedShortAxis (I := I) U b S.value))

local instance instNeZeroNatReferenceRetainedCRTModulusPath_1_r632f34_1 (cutoff : ℕ) :
    NeZero (slice.path.referenceRetainedCRTModulus cutoff) :=
  ⟨(slice.path.referenceRetainedCRTModulus_pos cutoff).ne'⟩
variable (cutoff : ℕ)
local notation "q" => slice.path.referenceRetainedCRTModulus cutoff
local notation "vol" => (∏ a, (basisAxisScale (b (Sigma.fst (selected a))) (Sigma.snd (selected a)) : ℝ))
local notation "grid" => forecastInactiveFixedOutput B U b S selected
  (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample) slice.path.commonTuple
local notation "Y" => (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
  (fun k => (z (Prod.fst k) (Prod.snd k) : ℤ)) q t j)

omit [Fintype Tsp] in

theorem retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2
    {Icap : ℝ}
    (hgrid : ∀ z : A → ℤ, vol * slice.principalLaw.fiberMean grid
      (fun a _ => z a) (fun _ => 1) ≤ Icap)
    (r : X → ZMod q) (β : Fin d → ℤ) :
    |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤
      Icap * (q : ℝ) ^ Fintype.card Out := by
  sorry

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
