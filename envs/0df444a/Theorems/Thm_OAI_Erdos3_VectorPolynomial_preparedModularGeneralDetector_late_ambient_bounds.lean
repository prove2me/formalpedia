-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedModularGeneralDetector_late_ambient_bounds
-- name    : OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_late_ambient_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T12:54:16.959717+00:00
-- url     : https://prove2.me/theorems/0a098bd2-1c62-4560-afec-880145ae8a41
-- title:
--   The general detector resources satisfy the late ambient bounds
-- statement:
--   Fix natural numbers $m$ and $\mathrm{dim}$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ for $j \in \mathrm{Fin}\,m$; finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, (I_j \oplus \mathrm{Fin}\,n_j)$); finite sets $\mathrm{rowSets}_j$ of subsets of $\mathrm{Fin}\,\mathrm{dim}$; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complement of $V_j = $ `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` (a structure bundling a positive natural number `S.value` with width and gap inequalities); functions $C_{\mathrm{forward}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ and a constant $K_{\mathrm{source}} \in \mathbb R_{\ge 0}$; and assume each lattice section $\mathbb Z^{J_j} \cap V_j$ is a full lattice in $V_j$ (`IsZLattice`).
--
--   Let $K$ be a `PreparedModularCanonicalDetectorResourceConstants` (a structure of natural-number constants, among them `K.m`) with `K.m` $= m$, and let $P, L, D$ be reals with $P \le L$, `AllocatedComparisonDimensions B (Fin dim) (fun j => rowSets j) D` (OpenAI's predicate that $D \ge 0$ bounds $m$, $|G|$, $\mathrm{dim}$ and a list of cardinalities of the layer-sampler index types) and $D \le P$. Assume $0 < R_j \le 1$ and $R_j^{-1} \le e^{P}$ for every $j$; $\texttt{S.value} \le e^{L}$; $|J_j| \le P$ for every $j$; `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le e^{P}$ for every $j$ (the covolume of $\mathbb Z^{J_j} \cap V_j$ divided by the product of the `basisAxisScale` of the vectors of $b_j$); $C_{\mathrm{forward}}(j) \le e^{P}$ for every $j$; $K_{\mathrm{source}} \le e^{P}$; and `normalizedSiteCutoffBound` $\le e^{P}$ (a fixed constant of OpenAI). Then `PreparedModularGeneralLateAmbientBounds B rowSets U b S Cforward Ksource (preparedModularGeneralDetectorResources K dim P L)` holds: the resource record `preparedModularGeneralDetectorResources K dim P L` (explicit real quantities `Pbox`, `Vlog`, `Nlog`, `baseAmbient`, … built by OpenAI from $K$, $\mathrm{dim}$, $P$, $L$) satisfies OpenAI's list of bounds `PreparedModularGeneralLateAmbientBounds` — nonnegativity of `Pbox`, `Vlog`, `Nlog`, `baseAmbient`; $2\,$`allocatedRowSlicedSiteRadius rowSets` $\le e^{\texttt{Pbox}}$; `allocatedFullGridNaturalVolume B U b S rowSets` $\le e^{\texttt{Vlog}}$; $\|(\texttt{allocatedProductIdealNormalizer B U b S rowSets})^{-1}\| \le e^{\texttt{Nlog}}$; $\texttt{Vlog}, \texttt{Nlog}, |\mathcal P(\mathrm{Fin}\,\mathrm{dim})|, |\texttt{LayerSamplerAxis I n}|, |\Sigma_a \mathrm{rowSets}_{a.1}| \le \texttt{baseAmbient}$; and $K_{\mathrm{source}}$, $\sum_j C_{\mathrm{forward}}(j)|J_j|$, `normalizedSiteCutoffBound`, $\sum_j |\mathrm{rowSets}_j|$ and $\texttt{S.value}^{\texttt{layerTailDegree}\ m + 1}$ are each $\le e^{\texttt{baseAmbient}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_late_ambient_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedModularCanonicalDetectorAmbientConsumer.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B199` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedModularCanonicalDetectorAmbientConsumer.lean#L456

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B199

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin 1)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)


variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)


variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem preparedModularGeneralDetector_late_ambient_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m) {P L D : ℝ}
    (hPL : P ≤ L)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hS : (S.value : ℝ) ≤ Real.exp L)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P)
    (hforward : ∀ j, (Cforward j : ℝ) ≤ Real.exp P) (hK : (Ksource : ℝ) ≤ Real.exp P)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp P) :
    PreparedModularGeneralLateAmbientBounds B rowSets U b S Cforward Ksource
      (preparedModularGeneralDetectorResources K dim P L) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
