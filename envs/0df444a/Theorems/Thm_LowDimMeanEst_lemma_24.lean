-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_24
-- name    : LowDimMeanEst.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:58:49.232199+00:00
-- url     : https://prove2.me/theorems/4cd4ed8d-0654-46f3-981d-890d245b83ad
-- title:
--   Lemma 24 — under events B and T, the samples with $\|x_i\|>\sqrt{nd}$ contribute $O(1)$ to $\sum(1-w_i)x_i^\top Ax_i$ and $O(\sqrt{(1+d/\log(1/\delta))/n})$ to the trimmed mean
-- statement:
--   **Lemma 24.** There is a universal constant $C>0$ such that the following holds. Let $d,n\ge1$, $\delta\in(0,\frac13]$, $\tau=\sqrt{nd}$, samples $x_1,\dots,x_n\in\mathbb R^d$ and a trimming matrix $A$ for them and $\delta$. If the samples satisfy event B (for $A$) and event T, then, with $w_i=\min(1,x_i^\top Ax_i)$,
--
--   $$\sum_{i:\|x_i\|>\tau}(1-w_i)\,x_i^\top Ax_i\ \le\ C,$$
--
--   and for every unit vector $z$,
--
--   $$\Big|\frac1n\sum_{i:\|x_i\|>\tau}(1-w_i)(x_i\cdot z)\Big|\ \le\ C\sqrt{\frac{1+d/\log(1/\delta)}{n}} .$$
--
--   The statement is deterministic. It bounds the contribution of the large-norm samples, which the net argument of Theorem 26 cannot handle directly.
--
--   **Formalization Note** Both $O(\cdot)$ are one universal constant $C$ chosen first.
--
--   Differences from the source:
--   - generalization: the trimming matrix A computed by Algorithm 2 (Lemma 3) → every A with IsTrimmingMatrix: A ⪰ 0, Σ min(1, x_i^⊤Ax_i) = (1/3)log(1/δ), Lemma 3's maximality; reason: the computed matrix has these properties (Lemma 3 and the weight sum of Algorithm 2), so the statement specializes to it; A is not unique (p.9)
--   - reading: event B: α ≤ O(1 + d/log(1/δ)) (Definition 22) → α ≤ (10¹⁰/3)(1 + d/log(1/δ)), α the largest trimmed empirical variance (1/n)Σ(1 − min(1, x_i^⊤Ax_i))⟨x_i, v⟩²; reason: Definition 22 refers to the bound established in Lemma 44, which is Lemma 43 applied with Tr(A) ≥ 10⁻¹⁰ log(1/δ)/(n(1 + d/log(1/δ))) (p.84); α read as in Lemma 43's proof
--   - encoding: d, n implicit → 1 ≤ d and 1 ≤ n; reason: standing assumptions: d ≥ 1 (p.13, Lemma 25) and n samples; only excludes degenerate cases
--   - encoding: δ ≤ 1/3 → 0 < δ ≤ 1/3; reason: δ is a probability parameter
--   - encoding: O(1) and O(√((1 + d/log(1/δ))/n)) → one universal constant C chosen before d, n, δ, x, A; reason: universal constants
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 24, pp.28–29 (proof pp.29–30)

import Mathlib
import Definitions.Def_LowDimMeanEst_Events

namespace LowDimMeanEst

/-- **Lemma 24**, pp.28–29 (proof pp.29–30).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Take the parameter τ as given in Table 1. Consider n samples x₁, …, xₙ ∈ ℝᵈ, along with the
trimming matrix A implicitly computed by Algorithm 2 (Lemma 3) with input {xᵢ} and parameter
δ ≤ 1/3. If the samples x₁, …, xₙ satisfy event B and event T with parameter δ, then it follows that
both Σ_{i:∥xᵢ∥>τ} (1 − min(1, xᵢ⊤Axᵢ)) xᵢ⊤Axᵢ ≤ O(1), and for all unit vectors z,
|(1/n) Σ_{i:∥xᵢ∥>τ} (1 − min(1, xᵢ⊤Axᵢ))(xᵢ · z)| ≤ O(√((1 + d/log(1/δ))/n))."

**Formalization Note.** Both `O(·)` are one universal constant `C`, chosen first. `τ = √(nd)`
(Table 1). "The trimming matrix" is any `A` with `IsTrimmingMatrix x δ A`; events B and T are
Definitions 22 and 21. Deterministic. `d ≥ 1`, `n ≥ 1`, `δ > 0` are standing assumptions.
-/
theorem lemma_24 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ ≤ 1 / 3 →
        ∀ (x : Fin n → E d) (A : E d →L[ℝ] E d), IsTrimmingMatrix x δ A → EventB x δ A →
          EventT x δ →
          ∑ i ∈ Finset.univ.filter (fun i => paramTau d n < ‖x i‖),
              (1 - trim A (x i)) * quad A (x i) ≤ C ∧
            ∀ z : E d, ‖z‖ = 1 →
              |(1 / (n : ℝ)) * ∑ i ∈ Finset.univ.filter (fun i => paramTau d n < ‖x i‖),
                  (1 - trim A (x i)) * inner ℝ (x i) z| ≤
                C * Real.sqrt ((1 + d / logInv δ) / n) := by sorry

end LowDimMeanEst
