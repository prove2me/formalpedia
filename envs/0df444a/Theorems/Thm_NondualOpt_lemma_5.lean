-- Prove2me | Theorems.Thm_NondualOpt_lemma_5
-- name    : NondualOpt.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:06.944215+00:00
-- url     : https://prove2.me/theorems/ffd17791-700c-452a-a742-aab09d3d97a1
-- title:
--   Lemma 5 — convex hull-distance to capped-simplex process
-- statement:
--   Suppose $\Lambda_{X,H}=1$. For a realized path $y_t=(g_t,b_t)\in Z_{X,H}$, $t=1,\dots,T$, with predictable laws $P_t=P_t(\cdot\mid y_{1:t-1})$ and predictable means $\mu_t,\beta_t$, define
--   $$
--   G_{X,H,T}(y_{1:T})=\sup_{u\in X}\Big\{\Big\langle\frac1T\sum_t\mu_t,u\Big\rangle+\frac1T\sum_t\beta_t-\max_{\lambda\in\Delta_T}\sum_t\lambda_t(\langle g_t,u\rangle+b_t)\Big\}.
--   $$
--   Then for every realized path
--   $$
--   G_{X,H,T}(y_{1:T})\le2\sup_{f\in\Phi\circ(\frac12A_{X,H})}\Big[\frac1T\sum_{t=1}^TP_tf-\frac2T\sum_{t=1}^Tf(y_t)\Big].
--   $$
--   The convex-hull approximation functional is dominated by a one-sided offset empirical process, which Proposition 20 bounds by chaining.
--
--   Differences from the source:
--   - generalization: Λ_{X,H} = 1, path in Z_{X,H} → |⟨g, u⟩| ≤ 1 for g ∈ H, u ∈ X; path in H × [−1, 1]; reason: the proof uses only these bounds; Λ_{X,H} = 1 gives Z_{X,H} = H × [−1, 1] and the bound
--   - generalization: E a real Banach space, H ⊆ E∗ bounded with the duality pairing, X closed and bounded with 0 ∈ X (§2 standing setting) → real vector spaces E, F with an abstract bilinear pairing, Λ_{X,H} < ∞, no closedness or boundedness of X and no 0 ∈ X; reason: the proofs use H only through pairings ⟨g, u⟩ and the bound Λ_{X,H} (footnote 7); the duality pairing between E∗ and E with bounded H is the instance F = E∗
--   - encoding: sup over u ∈ X of the left side → the inequality for every u ∈ X; reason: the right side does not depend on u
--   - encoding: ⟨(1/T)Σµ_t, u⟩ + (1/T)Σβ_t and max over λ ∈ Δ_T → (1/T)Σ_t ∫(⟨g, u⟩ + b) dP_t and max over t; reason: footnote 7's weak means; a linear function on Δ_T is maximized at a vertex
--   - encoding: kernels P_t(· | y_{1:t−1}) evaluated along the path, natural σ-algebras (footnote 5) → arbitrary probability measures P_t on H × [−1, 1] with a σ-algebra making each affine evaluation measurable; a real supremum over the class as a type; reason: the lemma is pathwise; the family lies in [−4, 2]
--   - encoding: rounds t = 1, …, T → T ≥ 1, rounds Fin T (0-based); reason: the statement divides by T and takes a maximum over [T]
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Lemma 5, p.11 (G_{X,H,T}, µ_t, β_t defined on pp.10–11)

import Mathlib
import Definitions.Def_NondualOpt_unitZ
import Definitions.Def_NondualOpt_offsetClass

open MeasureTheory

namespace NondualOpt

/-- **Lemma 5 (Convex hull-distance to capped-simplex process).** Suppose `Λ_{X,H} = 1`. For every
realized path `y_1, …, y_T ∈ Z_{X,H}` and the predictable laws `P_t = P_t(· | y_{1:t−1})`,
`G_{X,H,T}(y_{1:T}) ≤ 2 sup_{f ∈ Φ∘(½A_{X,H})} [(1/T)∑_t P_t f − (2/T)∑_t f(y_t)]`, where
`G_{X,H,T}(y_{1:T}) = sup_{u ∈ X} {⟨(1/T)∑_t µ_t, u⟩ + (1/T)∑_t β_t − max_{λ ∈ Δ_T} ∑_t λ_t(⟨g_t, u⟩ + b_t)}`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Lemma 5, p.11 (with `G_{X,H,T}` and the
predictable means `µ_t, β_t` defined on pp.10–11).

**Formalization Note.** (i) `Λ_{X,H} = 1` is generalized to `|⟨g, u⟩| ≤ 1` on `H × X`, the only
property the proof uses, and the path lies in `H × [−1, 1]`. (ii) `⟨(1/T)∑µ_t, u⟩ + (1/T)∑β_t` is
`(1/T)∑_t ∫ (⟨g, u⟩ + b) dP_t` (footnote 7's weak means), and the maximum of a linear function over
`Δ_T` is the maximum over its vertices; the supremum over `u ∈ X` is stated for every `u ∈ X`.
(iii) The `P_t` are any probability measures (the lemma is pathwise), on a measurable space on
`H × [−1, 1]` making every affine evaluation measurable (footnote 5). The supremum over the class is
a real `⨆` over the subtype; the family is bounded in `[−4, 2]`. Rounds are 0-based. -/
theorem lemma_5 {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F)
    (hΛ : ∀ g ∈ H, ∀ u ∈ X, |pair g u| ≤ 1) [MeasurableSpace (unitZ H)]
    (hmeas : ∀ u ∈ X, Measurable (fun z : unitZ H => pair (z : F × ℝ).1 u + (z : F × ℝ).2))
    (T : ℕ) (hT : 1 ≤ T) (y : Fin T → unitZ H) (P : Fin T → Measure (unitZ H))
    [∀ t, IsProbabilityMeasure (P t)] :
    ∀ u ∈ X, (1 / T : ℝ) * ∑ t, ∫ z, (pair (z : F × ℝ).1 u + (z : F × ℝ).2) ∂(P t) -
        ⨆ t, (pair (y t : F × ℝ).1 u + (y t : F × ℝ).2) ≤
      2 * ⨆ h : offsetClass pair X H, ((1 / T : ℝ) * ∑ t, ∫ z, (h : unitZ H → ℝ) z ∂(P t) -
        (2 / T : ℝ) * ∑ t, (h : unitZ H → ℝ) (y t)) := by sorry

end NondualOpt
