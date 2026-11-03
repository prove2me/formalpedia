-- Prove2me | Theorems.Thm_MultiPurchaseMNL_property_2_2
-- name    : MultiPurchaseMNL.property_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:12:54.981282+00:00
-- url     : https://prove2.me/theorems/2e8b4d90-9ea8-48ab-9787-8ff67fedb1f7
-- title:
--   Property 2.2 — conditional independence of top-ranked products
-- statement:
--   Let $e_0,e_1,\dots,e_n$ be independent standard Gumbel shocks and $U_i=v_i+e_i$ the random utilities, with $v_0=0$. Let $S_1$ and $S_2=\{j_1,\dots,j_p\}$ be disjoint sets of options (products or the no-purchase option). Then the order of the utilities inside $S_2$ is independent of the event that every option of $S_1$ beats every option of $S_2$:
--   $$
--   \Pr\Big[U_{j_1}>\dots>U_{j_p}\ \wedge\ \min_{i\in S_1}U_i>\max_{j\in S_2}U_j\Big]=\Pr\big[U_{j_1}>\dots>U_{j_p}\big]\cdot\Pr\Big[\min_{i\in S_1}U_i>\max_{j\in S_2}U_j\Big].
--   $$
--   This is the paper's conditional statement $\Pr[U_{j_1}>\dots>U_{j_p}\mid \min_{S_1}U>\max_{S_2}U]=\Pr[U_{j_1}>\dots>U_{j_p}]$ in product form. Together with Property 2.1 it is what the proof of Lemma 1 uses.
--
--   **Formalization Note** The list $j_1,\dots,j_p$ enumerates $S_2$ without repetition, and "$U_{j_1}>\dots>U_{j_p}$" is the pairwise condition along the list. "$\min_{S_1}U>\max_{S_2}U$" is $U_b<U_a$ for all $a\in S_1$, $b\in S_2$.
--
--   Differences from the source:
--
--   - encoding: Pr[A | B] = Pr[A] → Pr[A ∩ B] = Pr[A]·Pr[B]; reason: equivalent whenever Pr[B] > 0, and defined without dividing by Pr[B]
--   - generalization: S₁, S₂ a partition of an assortment S ⊆ [n] → any disjoint S₁, S₂ ⊆ Option (Fin n), possibly containing the no-purchase option, for every weight vector w; reason: the proof of Lemma 1 applies the property to S ∪ {0}; the paper's case is S₁ ∪ S₂ ⊆ [n] with w > 0
--   - encoding: U_{j₁} > ⋯ > U_{j_p}; min_{i∈S₁} Uᵢ > max_{j∈S₂} Uⱼ → l.Pairwise (U b < U a) for a list l enumerating S₂ without repetition; ∀ a ∈ S₁, ∀ b ∈ S₂, U b < U a; reason: the same events; the second is also defined when S₁ or S₂ is empty
--   - encoding: products 1..n and the no-purchase option 0; Uᵢ = vᵢ + eᵢ with e₀,…,eₙ i.i.d. standard Gumbel (0,1), v₀ = 0; wᵢ = e^{vᵢ} → products Fin n, option 0 = none : Option (Fin n); shocks under Measure.pi of μ with IsExtremeValue μ; vᵢ = log wᵢ with wᵢ > 0, so w₀ = 1; reason: same model: wᵢ = e^{vᵢ} > 0 is exactly vᵢ = log wᵢ, and IsExtremeValue is the standard Gumbel cdf
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), Property 2.2, p.10

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), **Property 2.2** (Conditional
Independence of Top Ranked Products), p.10: if `S₁` and `S₂ = {j₁, …, j_p}` partition an assortment
`S`, then `Pr[U_{j₁} > ⋯ > U_{j_p} | min_{i∈S₁} Uᵢ > max_{j∈S₂} Uⱼ] = Pr[U_{j₁} > ⋯ > U_{j_p}]`.

**Formalization Note.** Stated in product form `Pr[A ∩ B] = Pr[A] · Pr[B]`, which needs no
`Pr[B] > 0`. `S₁`, `S₂` are disjoint sets of options that may contain the no-purchase option
`none` (the proof of Lemma 1 applies the property to `S ∪ {0}`). The list `l` enumerates `S₂`
without repetition; "`U_{j₁} > ⋯ > U_{j_p}`" is `l.Pairwise` of `>` on utilities, and
"`min_{S₁} U > max_{S₂} U`" is `∀ a ∈ S₁, ∀ b ∈ S₂, U_b < U_a`. The weights `w` are arbitrary:
`vᵢ = log wᵢ` is some real number for every `w`. -/
theorem property_2_2 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : McFadden1974.RandomUtility.IsExtremeValue μ) {n mmax : ℕ} (I : Instance n mmax)
    (S₁ S₂ : Finset (Option (Fin n))) (hdisj : Disjoint S₁ S₂)
    (l : List (Option (Fin n))) (hl : l.Nodup) (hlS : l.toFinset = S₂) :
    shockLaw μ n {e | l.Pairwise (fun a b => utility I e b < utility I e a) ∧
        ∀ a ∈ S₁, ∀ b ∈ S₂, utility I e b < utility I e a} =
      shockLaw μ n {e | l.Pairwise (fun a b => utility I e b < utility I e a)} *
        shockLaw μ n {e | ∀ a ∈ S₁, ∀ b ∈ S₂, utility I e b < utility I e a} := by sorry

end MultiPurchaseMNL
