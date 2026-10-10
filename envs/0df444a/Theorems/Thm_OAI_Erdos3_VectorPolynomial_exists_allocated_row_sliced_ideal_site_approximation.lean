-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_row_sliced_ideal_site_approximation
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_row_sliced_ideal_site_approximation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T21:17:44.960962+00:00
-- url     : https://prove2.me/theorems/e5b35604-718e-4ad6-90d4-b9d782d21672
-- title:
--   The row-sliced ideal density is approximated by sums of products of site factors
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$; write $N_{\mathrm{ax}}$ for its cardinality), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let $\alpha$ be a finite type with decidable equality and $\mathrm{rowSets}_j$ finite sets of finite subsets of $\alpha$; write $\mathrm{jets}_j$ for the subtype of members of $\mathrm{rowSets}_j$. Let grid be `allocatedGridAxis U b S.value` (a predicate on `LayerSamplerAxis I n`) and let center, width be real functions on `PrincipalAxisParameter (¬grid)` (with block types $B$ and degrees `layerSamplerDegree I n`). Assume $R_j > 0$ for all $j$; let $\delta$ be a nonnegative real with $0 < \delta \le 1$; assume $|\mathrm{center}(i)| + |\mathrm{width}(i)| \le 1$ for all $i$; let $\varepsilon, p$ be reals with $0 < \varepsilon$, $0 \le p$, $2\,r \le \exp p$, $\varepsilon^{-1} \le \exp p$ and $\delta^{-1} \le \exp p$, where $r =$ `allocatedRowSlicedSiteRadius rowSets` (the nonnegative real $1 + \sum_j |\mathrm{rowSets}_j|\,(\texttt{partitionedIdealRadius}\ \alpha\ m + 1)$). Put $C = N_{\mathrm{ax}} \cdot$ `normalizedSiteCutoffBound` $/(2r)$ (a nonnegative real; `normalizedSiteCutoffBound` is a constant chosen by OpenAI), $Q =$ `idealSiteLogBudget` $K$ $|\alpha|$ $p$ with $K = |\Sigma_{a}\, \mathrm{jets}_{a.1}|$ (sum over $a \in$ `LayerSamplerAxis I n`), $V = \prod_{q} R_{q.1.1}$ over $q \in \Sigma_{a : \{a \mid \neg\,\mathrm{grid}\,a\}} \mathrm{jets}_{a.1}$, $X = \mathrm{Finset}\,\alpha \times$ `LayerSamplerAxis I n`, and $L = |\mathrm{Finset}\,\alpha| \cdot N_{\mathrm{ax}}$. Then there is $k \in \mathbb N$ with $k \le \exp(4Q+8)$ and $|X \to \mathrm{Fin}\,k| \le \exp(L(4Q+8))$, together with $a : (X \to \mathrm{Fin}\,k) \to \mathbb C$ and $f : (X \to \mathrm{Fin}\,k) \to \mathrm{Finset}\,\alpha \to (\mathbb R^{\texttt{LayerSamplerAxis I n}} \to \mathbb C)$, such that: $\sum_i \|a_i\| \le \exp(L(4Q+8) + Q)$; $\|f_{i,s}(v)\| \le 1$ for all $i, s, v$; each $f_{i,s}$ is Lipschitz (for the sup norm) with constant $\exp(N_{\mathrm{ax}} + 6Q + 12) + C$; $f_{i,s}(v) = 0$ whenever some coordinate has $2r < |v_d|$; and for every $z \in$ `AllocatedLongJetRows B U b S jets`, writing $\Phi(z) =$ `allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z)` (cast to $\mathbb C$) and $\Sigma(z) = \sum_i a_i \prod_{s \in \mathrm{Finset}\,\alpha} f_{i,s}(\texttt{allocatedRowIdealCoordinates B U b S rowSets z s})$, both $\|V\,\Phi(z) - \Sigma(z)\| \le \varepsilon$ and $\|\Phi(z) - \Sigma(z)/V\| \le \varepsilon / V$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_row_sliced_ideal_site_approximation` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedRowSlicedIdealApproximation.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B144` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedRowSlicedIdealApproximation.lean#L90

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B144

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (rowSets : Fin m → Finset (Finset α))

local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "siteRadius" => allocatedRowSlicedSiteRadius rowSets
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

theorem exists_allocated_row_sliced_ideal_site_approximation (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (siteRadius : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let radius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) (Fintype.card α) p
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + C) (f i s)) ∧
        (∀ i s v, (∃ d, 2 * (radius : ℝ) < |v d|) → f i s v = 0) ∧
        ∀ z : AllocatedLongJetRows B U b S jets,
          ‖(volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)‖ ≤ ε ∧
          ‖(allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            (∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ ≤ ε / volume := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
