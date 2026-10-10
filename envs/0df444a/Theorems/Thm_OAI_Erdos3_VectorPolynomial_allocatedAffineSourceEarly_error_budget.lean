-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineSourceEarly_error_budget
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineSourceEarly_error_budget
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T09:48:08.714782+00:00
-- url     : https://prove2.me/theorems/6116b044-a040-4bab-91c4-590fc135379d
-- title:
--   Grid and long accuracies chosen from the budget make the early affine error tiny
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ and finite families $\mathrm{rowSets}_j$ of finsets of $\alpha$ (rowTypes$_j$ is the subtype of $\mathrm{rowSets}_j$); finite types $E_j$; and each $\Lambda_j =$ `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` a $\mathbb Z$-lattice (`IsZLattice`). Assume $R_j > 0$ for all $j$ (hR), and let $P_{\mathrm{num}} \ge 0$ (hPnum) with $|I_j| \le P_{\mathrm{num}}$ (hI), $n_j \le P_{\mathrm{num}}$ (hn), $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \le P_{\mathrm{num}}$ (hcoeff), $R_j^{-1} \le e^{P_{\mathrm{num}}}$ (hRi) and `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le e^{P_{\mathrm{num}}}$ (hV) for all $j$. Let grid be the predicate `allocatedGridAxis U b S.value` and outputs $= \Sigma_{a\ \text{non-grid}}\,\mathrm{rowTypes}_{\mathrm{layer}(a)}$.
--
--   Let $M_k, \mathrm{period} \in \mathbb N$ and reals $P_k, P_{\mathrm{per}}, P_\rho, \mathrm{target} \ge 0$ and $O_p$, with $M_k \le e^{P_k}$ and $\mathrm{period} \le e^{P_{\mathrm{per}}}$, and let $\rho \in \mathbb R_{\ge 0}$ with $\rho^{-1} \le e^{P_\rho}$. Put
--   $F = m\,2^{|\alpha|}(P_{\mathrm{num}}+8)(1+4P_{\mathrm{num}}) + |\texttt{LayerSamplerAxis I n}|\cdot m\,2^{m+1}P_k + \sum_j |E_j|\cdot|\mathrm{rowTypes}_j|\cdot P_{\mathrm{per}}$, $D_{\mathrm{out}} = |\Sigma_a\,\mathrm{rowTypes}_{\mathrm{layer}(a)}|$ (over all axes), $D_{\mathrm{grid}} = |\texttt{LayerSamplerAxis I n}|$, $P_{\mathrm{box}} = (m+2)|\alpha| + m + 4$, $\varepsilon_{\mathrm{grid}} = \exp(-(D_{\mathrm{out}}P_\rho + \mathrm{target} + F + 1))$, $G_{\mathrm{cost}} = D_{\mathrm{grid}}\max(O_p, 0)$, $\varepsilon_{\mathrm{long}} = \exp(-(G_{\mathrm{cost}} + \mathrm{target} + F + 1))$ and $P_{\mathrm{long}} = P_{\mathrm{box}} + P_\rho + G_{\mathrm{cost}} + \mathrm{target} + F + 2$. Then all of the following hold: $0 < \varepsilon_{\mathrm{grid}} \le 1$ and $\varepsilon_{\mathrm{grid}}^{-1} = \exp(D_{\mathrm{out}}P_\rho + \mathrm{target} + F + 1)$; $0 < \varepsilon_{\mathrm{long}} \le 1$ and $\varepsilon_{\mathrm{long}}^{-1} \le e^{P_{\mathrm{long}}}$; $0 \le P_{\mathrm{long}}$; $2\cdot$`allocatedRowSlicedSiteRadius rowSets` $\le e^{P_{\mathrm{long}}}$ (the radius is $1 + \sum_j |\mathrm{rowSets}_j|(\texttt{partitionedIdealRadius α m} + 1)$); $\rho^{-1} \le e^{P_{\mathrm{long}}}$; and
--   $$\bigl\|\texttt{allocatedProductIdealNormalizer B U b S rowSets}^{-1}\bigr\|\cdot\bigl(\texttt{layerKernelIndexBound m Mk}^{|\texttt{LayerSamplerAxis I n}|}\cdot\texttt{coefficientDeckPeriodCap rowTypes E period}\bigr)\cdot\Bigl(\rho^{-|\mathrm{outputs}|}\varepsilon_{\mathrm{grid}} + \varepsilon_{\mathrm{long}}\prod_{a\ \text{grid}} e^{O_p}\Bigr) \le e^{-\mathrm{target}},$$
--   where `layerKernelIndexBound m Mk` $= M_k^{m 2^{m+1}}$ and `coefficientDeckPeriodCap rowTypes E period` $= \prod_j\mathrm{period}^{|E_j|\cdot|\mathrm{rowTypes}_j|}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineSourceEarly_error_budget` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineSourceAccuracy.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B198` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineSourceAccuracy.lean#L79

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

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

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "outputs" => (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a)))

include hR hPnum hI hn hcoeff hRi hV in
omit [DecidableEq α] in
theorem allocatedAffineSourceEarly_error_budget
    {Mk period : ℕ} {Pk Pper Prho target Op : ℝ}
    (hPk : 0 ≤ Pk) (hPper : 0 ≤ Pper) (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target)
    (hMk : (Mk : ℝ) ≤ Real.exp Pk) (hperiod : (period : ℝ) ≤ Real.exp Pper)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho) :
    let F := (m * (2 : ℝ) ^ Fintype.card α) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * Pper)
    let Dout := (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ)
    let Dgrid := (Fintype.card (LayerSamplerAxis I n) : ℝ)
    let Pbox := ((m : ℝ) + 2) * Fintype.card α + m + 4
    let εgrid := Real.exp (-(Dout * Prho + (target + F) + 1))
    let Gcost := Dgrid * max Op 0
    let εlong := Real.exp (-(Gcost + (target + F) + 1))
    let Plong := Pbox + Prho + Gcost + (target + F) + 2
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Dout * Prho + (target + F) + 1) ∧
      0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp Plong ∧ 0 ≤ Plong ∧
      2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Plong ∧
      (ρ : ℝ)⁻¹ ≤ Real.exp Plong ∧
      ‖inverseNormalizer‖ *
        ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
          coefficientDeckPeriodCap rowTypes E period) *
        ((ρ⁻¹ ^ Fintype.card outputs : ℝ≥0) * εgrid +
          εlong * ∏ _a : {a // grid a}, Real.exp Op) ≤ Real.exp (-target) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
