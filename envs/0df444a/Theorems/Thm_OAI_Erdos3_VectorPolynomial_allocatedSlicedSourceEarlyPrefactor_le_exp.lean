-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedSourceEarlyPrefactor_le_exp
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSlicedSourceEarlyPrefactor_le_exp
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T09:18:37.780973+00:00
-- url     : https://prove2.me/theorems/2620ca6e-e368-4c46-81f6-74d4ded3782d
-- title:
--   The early sliced-source prefactor is at most an explicit exponential
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ and finite families $\mathrm{rowSets}_j$ of finsets of $\alpha$ (rowTypes$_j$ is the subtype of $\mathrm{rowSets}_j$); finite types $E_j$; and each $\Lambda_j =$ `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` a $\mathbb Z$-lattice (`IsZLattice`). Assume $R_j > 0$ for all $j$ (hR), and let $P_{\mathrm{num}} \ge 0$ (hPnum) with $|I_j| \le P_{\mathrm{num}}$ (hI), $n_j \le P_{\mathrm{num}}$ (hn), $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \le P_{\mathrm{num}}$ (hcoeff), $R_j^{-1} \le e^{P_{\mathrm{num}}}$ (hRi) and `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le e^{P_{\mathrm{num}}}$ (hV; the covolume of $\Lambda_j$ divided by $\prod_i$ `basisAxisScale (b j) i`) for all $j$.
--
--   Let $M_k, \mathrm{period} \in \mathbb N$ and $P_k, P_{\mathrm{per}} \in \mathbb R$ with $M_k \le e^{P_k}$ and $\mathrm{period} \le e^{P_{\mathrm{per}}}$. Then
--   $$\bigl\|\texttt{allocatedProductIdealNormalizer B U b S rowSets}^{-1}\bigr\|\cdot\Bigl(\texttt{layerKernelIndexBound m Mk}^{|\texttt{LayerSamplerAxis I n}|}\cdot\texttt{coefficientDeckPeriodCap rowTypes E period}\Bigr)$$
--   $$\le \exp\Bigl(m\,2^{|\alpha|}(P_{\mathrm{num}}+8)(1+4P_{\mathrm{num}}) + |\texttt{LayerSamplerAxis I n}|\cdot m\,2^{m+1}P_k + \sum_j |E_j|\cdot|\mathrm{rowTypes}_j|\cdot P_{\mathrm{per}}\Bigr),$$
--   where `layerKernelIndexBound m Mk` $= M_k^{m 2^{m+1}}$, `coefficientDeckPeriodCap rowTypes E period` $= \prod_j \mathrm{period}^{|E_j|\cdot|\mathrm{rowTypes}_j|}$, and `allocatedProductIdealNormalizer B U b S rowSets` is a real number (a base volume times $\prod R_{\mathrm{layer}}$ over the non-grid output rows).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSlicedSourceEarlyPrefactor_le_exp` in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedCanonicalBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B198` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedCanonicalBudget.lean#L270

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (E : Fin m → Type*) [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (hR : ∀ j, 0 < R j) (C V : Fin m → ℝ≥0) {Pnum : ℝ}
variable (hnum : AllocatedSourceNumerics B U b S C V Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hR hnum hV

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (E : Fin m → Type*) [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
variable (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
variable (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum)

include hR hPnum hI hn hcoeff hRi hV

omit [DecidableEq α] in
theorem allocatedSlicedSourceEarlyPrefactor_le_exp
    {Mk period : ℕ} {Pk Pper : ℝ}
    (hMk : (Mk : ℝ) ≤ Real.exp Pk) (hperiod : (period : ℝ) ≤ Real.exp Pper) :
    ‖inverseNormalizer‖ * ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap rowTypes E period) ≤
    Real.exp ((m * (2 : ℝ) ^ Fintype.card α) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * Pper)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
