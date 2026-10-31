-- Prove2me | Theorems.Thm_InfHorizonVP_optimality_along_trajectory
-- name    : InfHorizonVP.optimality_along_trajectory
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:20.377431+00:00
-- url     : https://prove2.me/theorems/9a2df8f7-6c03-4022-ae22-33f55ff96319
-- title:
--   §B.2, §B.3 (unnumbered) — dynamic programming along an optimal trajectory
-- statement:
--   Let $E$ be a separable real Banach space, assume (H1)–(H7), and let $x_0\in\mathcal A_{(0,\xi)}$ be optimal for $(P_0)$. Then for all $0\le t\le T$,
--   $$
--   V(t,x_0(t))=\int_t^T L(s,x_0(s),\dot x_0(s))\,ds+V(T,x_0(T)).
--   $$
--
--   Tails of optimal trajectories are optimal; the proofs of Theorems 3.2 and 4.1 subtract this identity from the Bellman inequality for a perturbed arc.
--
--   **Formalization Note** The identity is in the extended reals.
--
--   Differences from the source:
--   - reading: the identities V(t, x0(t)) = ∫_t^{t+h} L + V(t + h, x0(t + h)) (p.28) and V(0, x0(0)) = ∫_0^t L + V(t, x0(t)) (p.31), used without statement → V(t, x₀(t)) = ∫_t^T L + V(T, x₀(T)) for all 0 ≤ t ≤ T, under (H1)–(H7); reason: both displays are instances
--   - encoding: functions on ℝ₊ = [0, ∞) → functions on ℝ with every condition restricted to [0, ∞) (derivatives and weak* derivatives at t > 0); reason: Lean convention; values at negative times are never used, same instances
--   - encoding: E* the norm dual; ẋ the strong derivative → E →L[ℝ] ℝ with the operator norm; deriv x; reason: Lean convention; same objects (deriv agrees with the strong derivative wherever it exists, which is a.e.)
--   - encoding: V : ℝ₊ × E → ℝ ∪ {±∞}, inf ∅ = +∞; improper integral as lim_{T→∞} ∫_t^T → EReal-valued valueFn (iInf, ⊤ for the empty family); the improper integral requires integrability on each [t, T] and an EReal limit; reason: Lean convention; integrability makes the finite integrals genuine and holds for every arc under (H2)–(H3)
--   - encoding: L : ℝ₊ × E × E → ℝ ∪ {+∞} → L : ℝ → E → E → ℝ; reason: (H3) bounds |L(t, 0, 0)| and makes L(t, ·, ·) Lipschitz, so L is finite everywhere
--   - encoding: there exist moduli l₁, l₂ (H3) and γ (H6) → l₁, l₂, γ as arguments with hypotheses HypH3, HypH6, HypH7 on the same functions; reason: a universally quantified hypothesis is equivalent to an existential one; the moduli are shared with (H7)
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, proof of Theorem 3.2, §B.2, p.28, and proof of Theorem 4.1, §B.3, p.31, display "Subtracting V(0, x0(0)) = ∫_0^t L(s, x0(s), ẋ0(s))ds + V(t, x0(t))"

import Mathlib
import Definitions.Def_InfHorizonVP_valueFn
import Definitions.Def_InfHorizonVP_HypH1
import Definitions.Def_InfHorizonVP_HypH2
import Definitions.Def_InfHorizonVP_HypH3
import Definitions.Def_InfHorizonVP_HypH4
import Definitions.Def_InfHorizonVP_HypH5
import Definitions.Def_InfHorizonVP_HypH6
import Definitions.Def_InfHorizonVP_HypH7
import Definitions.Def_InfHorizonVP_IsOptimal
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Optimality along an optimal trajectory (proofs of Theorems 3.2 and 4.1).**
Frankowska, Sagara, arXiv:1801.00400v3, used without statement in §B.2, p.28 ("Subtracting
V(t, x0(t)) = ∫_t^{t+h} L(s, x0(s), ẋ0(s))ds + V(t + h, x0(t + h)) from the both sides of the
above inequality yields") and §B.3, p.31 ("Subtracting V(0, x0(0)) = ∫_0^t L(s, x0(s), ẋ0(s))ds +
V(t, x0(t)) from the both sides of the above inequality yields").

Under (H1)–(H7), if `x₀ ∈ 𝒜_(0,ξ)` is optimal for `(P₀)`, then for all `0 ≤ t ≤ T`,
`V(t, x₀(t)) = ∫_t^T L(s, x₀(s), ẋ₀(s)) ds + V(T, x₀(T))`.

**Formalization Note.** The identity is in `EReal`; `ẋ₀ = deriv x₀`. -/
theorem optimality_along_trajectory {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (L : ℝ → E → E → ℝ) (Γ : ℝ → E → Set E) (l₁ l₂ γ : ℝ → ℝ)
    (hH1 : HypH1 Γ) (hH2 : HypH2 L) (hH3 : HypH3 L l₁ l₂) (hH4 : HypH4 Γ) (hH5 : HypH5 Γ)
    (hH6 : HypH6 Γ γ) (hH7 : HypH7 l₁ l₂ γ)
    (ξ : E) (x₀ : ℝ → E) (hopt : IsOptimal L Γ 0 ξ x₀) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    valueFn L Γ t (x₀ t) =
      (((∫ s in t..T, L s (x₀ s) (deriv x₀ s)) : ℝ) : EReal) + valueFn L Γ T (x₀ T) := by sorry

end InfHorizonVP
