-- Prove2me | Theorems.Thm_InfHorizonVP_theorem_3_1
-- name    : InfHorizonVP.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:16.051108+00:00
-- url     : https://prove2.me/theorems/c82315f6-012a-42e1-86eb-e0f2b03ed31e
-- title:
--   Theorem 3.1 — V is finite and lower semicontinuous; V(t, ·) is Lipschitz of rank k(t) → 0 (corrected: bounded on ℝ₊ × bounded sets)
-- statement:
--   Let $E$ be a separable real Banach space and assume (H1)–(H7). Then
--
--   1. $V(t,\xi)$ is finite for every $(t,\xi)\in\mathbb R_+\times E$;
--   2. for every $R$, $V$ is bounded on $\mathbb R_+\times\{\|\xi\|\le R\}$;
--   3. $V$ is lower semicontinuous on $\mathbb R_+\times E$;
--   4. there is a continuous, strictly decreasing $k:\mathbb R_+\to\mathbb R_+$ with $k(t)\to0$ as $t\to\infty$ such that for every $t\ge0$,
--   $$
--   |V(t,\xi)-V(t,\xi')|\le k(t)\|\xi-\xi'\|\qquad(\xi,\xi'\in E).
--   $$
--
--   The rank $k(t)\to0$ is what yields the transversality condition $p(t)\to0$ of Theorem 4.1, and the Lipschitz continuity of $V(t,\cdot)$ is used throughout the subdifferential estimates.
--
--   **Formalization Note** $V$ is extended-real valued; once finiteness is asserted, boundedness and the Lipschitz bound are stated on its real values.
--
--   Differences from the source:
--   - correction: V is bounded on R+ × E → V is finite everywhere and, for every R, bounded on ℝ₊ × {‖ξ‖ ≤ R}; reason: the printed claim is false: E = ℝ, Γ ≡ {0}, γ ≡ 0, L(t, x, y) = e^{−t}x, l₁(t) = e^{−t}, l₂ ≡ 0 satisfy (H1)–(H7) and give V(t, ξ) = ξe^{−t}, unbounded in ξ; the proof (§B.1, p.24) shows exactly finiteness and boundedness on bounded sets
--   - reading: continuous decreasing function k → k continuous on ℝ₊, nonnegative, strictly decreasing (StrictAntiOn); reason: the stronger of the two readings of 'decreasing'; k is existential and k(t) + e^{−t} is again a valid rank
--   - encoding: V lower semicontinuous on R+ × E → LowerSemicontinuousOn of (t, ξ) ↦ V(t, ξ) on [0, ∞) × E; reason: joint lower semicontinuity in the subspace topology, as on the page
--   - encoding: functions on ℝ₊ = [0, ∞) → functions on ℝ with every condition restricted to [0, ∞) (derivatives and weak* derivatives at t > 0); reason: Lean convention; values at negative times are never used, same instances
--   - encoding: E* the norm dual; ẋ the strong derivative → E →L[ℝ] ℝ with the operator norm; deriv x; reason: Lean convention; same objects (deriv agrees with the strong derivative wherever it exists, which is a.e.)
--   - encoding: V : ℝ₊ × E → ℝ ∪ {±∞}, inf ∅ = +∞; improper integral as lim_{T→∞} ∫_t^T → EReal-valued valueFn (iInf, ⊤ for the empty family); the improper integral requires integrability on each [t, T] and an EReal limit; reason: Lean convention; integrability makes the finite integrals genuine and holds for every arc under (H2)–(H3)
--   - encoding: L : ℝ₊ × E × E → ℝ ∪ {+∞} → L : ℝ → E → E → ℝ; reason: (H3) bounds |L(t, 0, 0)| and makes L(t, ·, ·) Lipschitz, so L is finite everywhere
--   - encoding: there exist moduli l₁, l₂ (H3) and γ (H6) → l₁, l₂, γ as arguments with hypotheses HypH3, HypH6, HypH7 on the same functions; reason: a universally quantified hypothesis is equivalent to an existential one; the moduli are shared with (H7)
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, Theorem 3.1, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_InfHorizonVP_valueFn
import Definitions.Def_InfHorizonVP_HypH1
import Definitions.Def_InfHorizonVP_HypH2
import Definitions.Def_InfHorizonVP_HypH3
import Definitions.Def_InfHorizonVP_HypH4
import Definitions.Def_InfHorizonVP_HypH5
import Definitions.Def_InfHorizonVP_HypH6
import Definitions.Def_InfHorizonVP_HypH7
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Theorem 3.1 — the value function is finite, lower semicontinuous, and `V(t, ·)` is Lipschitz
of rank `k(t) → 0` (corrected: bounded on ℝ₊ × bounded sets).**
Frankowska, Sagara, arXiv:1801.00400v3, Theorem 3.1, p.9: "If (H1)–(H7) hold, then V is bounded and
lower semicontinuous on R+ × E, and V(t, ·) is Lipschitz of rank k(t) on E for every t ∈ R+ with a
continuous decreasing function k : R+ → R+ satisfying k(t) → 0 as t → ∞."

**Formalization Note.** Correction: "V is bounded" is false as printed (`E = ℝ`, `Γ ≡ {0}`,
`γ ≡ 0`, `L(t, x, y) = e^{−t}x`, `l₁ = e^{−t}`, `l₂ = 0` satisfy (H1)–(H7) and give
`V(t, ξ) = ξe^{−t}`); what the proof (§B.1, p.24) shows is that `V` is real-valued and bounded on
`ℝ₊ × {‖ξ‖ ≤ R}` for every `R`, which is stated. "Decreasing" is read as strictly decreasing (the
stronger reading). Lower semicontinuity is joint, on `ℝ₊ × E`. `V` is `EReal`-valued; once it is
shown finite, the Lipschitz bound is stated on its real values. -/
theorem theorem_3_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (L : ℝ → E → E → ℝ) (Γ : ℝ → E → Set E) (l₁ l₂ γ : ℝ → ℝ)
    (hH1 : HypH1 Γ) (hH2 : HypH2 L) (hH3 : HypH3 L l₁ l₂) (hH4 : HypH4 Γ) (hH5 : HypH5 Γ)
    (hH6 : HypH6 Γ γ) (hH7 : HypH7 l₁ l₂ γ) :
    (∀ t, 0 ≤ t → ∀ ξ : E, valueFn L Γ t ξ ≠ ⊤ ∧ valueFn L Γ t ξ ≠ ⊥) ∧
    (∀ R : ℝ, ∃ M : ℝ, ∀ t, 0 ≤ t → ∀ ξ : E, ‖ξ‖ ≤ R → |(valueFn L Γ t ξ).toReal| ≤ M) ∧
    LowerSemicontinuousOn (fun q : ℝ × E => valueFn L Γ q.1 q.2) (Ici 0 ×ˢ univ) ∧
    ∃ k : ℝ → ℝ, ContinuousOn k (Ici 0) ∧ (∀ t, 0 ≤ t → 0 ≤ k t) ∧ StrictAntiOn k (Ici 0) ∧
      Tendsto k atTop (𝓝 0) ∧
      ∀ t, 0 ≤ t → ∀ ξ ξ' : E,
        |(valueFn L Γ t ξ).toReal - (valueFn L Γ t ξ').toReal| ≤ k t * ‖ξ - ξ'‖ := by sorry

end InfHorizonVP
