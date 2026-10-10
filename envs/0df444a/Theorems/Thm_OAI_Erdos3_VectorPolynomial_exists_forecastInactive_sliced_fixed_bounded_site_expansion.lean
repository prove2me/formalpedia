-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastInactive_sliced_fixed_bounded_site_expansion
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_bounded_site_expansion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T05:59:43.750354+00:00
-- url     : https://prove2.me/theorems/e4dd2b54-a59e-4ee1-9a7a-4d0f89a509dd
-- title:
--   A bounded site expansion approximates the shifted residue jet PMF on a grid axis
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ with decidable equality and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ with decidable equality; $q \in \mathbb N$ and $r : \mathrm{FullInput} \to \mathrm{Option}\,\alpha \to \mathbb Z/q$, where FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`; $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $\mathrm{lower} : \mathrm{FullInput} \to \mathbb Z$ with $H_t > 0$ (hH) and each progression `integerProgressionSupport (lower t) (step t) (H t)` $= \{\mathrm{lower}_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0,$ `allocatedPrincipalSides B U b S t`$)$ (hsubset); the residue cell $\{y : \texttt{principalResidueLabel q y} = r\}$ of positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hcell); and a layer $j$ with an index $i \in \mathrm{Fin}(n_j)$. Write scale $=$ `basisAxisScale (b j) i` $= \lceil\|b_j(i)\|^{-1}\rceil$ and radius $= |\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}|\cdot 2^{|\alpha|}(|\alpha|+1)^{j+1}R_j$.
--
--   Assume $\sigma_j \le 1$ and that the axis $\langle j,\mathrm{inr}\,i\rangle$ satisfies `allocatedGridAxis U b S.value` (hgrid). Let $c \in \mathbb Z$ with nonzero probability under the constant-coefficient law `allocatedLayerIntegerPMFs B U b hR hσ S j i (principalCoefficientChoice (layerSamplerDegree I n) ⟨j, inr i⟩ none)` (a PMF on $\mathbb Z$); let rows be a finset of finsets of $\alpha$; let $K_{\max} \in \mathbb N$ with scale $\le K_{\max}$; and let $\varepsilon > 0$, $P \ge 0$ with $|\mathrm{rows}|\cdot\mathrm{radius} + 1/4 \le e^P$, $K_{\max}^{|\mathrm{rows}|} \le e^P$, $|\mathrm{rows}|\cdot 2K_{\max}^2\cdot K_{\max}^{|\mathrm{rows}|}\cdot 2^{|\alpha|} \le e^P$ and $\varepsilon^{-1} \le e^P$. Then there exists a `ScalarSiteExpansion` $e$ on $\mathrm{Finset}\,\alpha$ (a finite family of terms $k$, each with a period $p_k$, a coefficient $a_k \in \mathbb C$ and factors $\phi_{k,s} : \mathbb Z/p_k \times \mathbb R \to \mathbb C$; its integer evaluation at height $N$ is $y \mapsto \sum_k a_k \prod_s \phi_{k,s}(y_s \bmod p_k, y_s/N)$) such that:
--
--   - `e.Bounds T 1 C L Hs` holds with $T = \exp(2^{|\alpha|}(4P+8))$, $C = \exp(2^{|\alpha|}(4P+8)+P)$, $L = \exp(1+6P+12) + 4$ and $Hs = |\mathrm{rows}|\cdot\mathrm{radius} + 1/4$: at most $T$ terms, periods in $(0, 1]$, $\sum_k|a_k| \le C$, every factor of norm at most $1$ and $L$-Lipschitz in its real argument, and vanishing at real arguments $x$ with $|x| \ge Hs$; and
--   - for every $y : \mathrm{Finset}\,\alpha \to \mathbb Z$ whose Möbius coefficients `booleanCoefficient y t` $= \sum_{u \subseteq t}(-1)^{|t \setminus u|}y(u)$ vanish for all $t \notin \mathrm{rows}$,
--   $$\Bigl\|\mathrm{scale}^{|\mathrm{rows}|}\cdot\texttt{allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r H step lower hH hsubset hcell j i rows}\ \mathrm{shift}\ (t \mapsto \texttt{booleanCoefficient y t}) - \texttt{e.integerEval scale y}\Bigr\| \le \varepsilon,$$
--   where $\mathrm{shift}(t) =$ `booleanCoefficient (fun _ => c) t` and the PMF (on $\mathrm{rows} \to \mathbb Z$) is the law of $\mathrm{shift} + \sum_{b} \mathrm{coeff}_b\cdot(\text{the integer Boolean block jet of the conditioned tuple at } \langle j, \mathrm{inr}\,i\rangle, b)$, with $\mathrm{coeff}$ drawn from the product of the layer integer PMFs at the principal slots and the tuple from `containedSupportedProgressionLaw … H step lower … hH hsubset q r hcell`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_bounded_site_expansion` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedAxisCap.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B055`, `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedAxisCap.lean#L65

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B145

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => j.val + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    R j
local notation "scale" => basisAxisScale (b j) i
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

theorem exists_forecastInactive_sliced_fixed_bounded_site_expansion
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (c : ℤ) (hc : constantLaw c ≠ 0)
    (rows : Finset (Finset α)) {Kmax : ℕ} (hKmax : scale ≤ Kmax)
    {ε P : ℝ} (hε : 0 < ε) (hP : 0 ≤ P)
    (hHP : rows.card * radius + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r H step lower hH hsubset hcell j i rows
            (fun t => booleanCoefficient (fun _ : Finset α => c) t)
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
