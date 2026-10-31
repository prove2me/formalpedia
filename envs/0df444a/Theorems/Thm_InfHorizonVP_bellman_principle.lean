-- Prove2me | Theorems.Thm_InfHorizonVP_bellman_principle
-- name    : InfHorizonVP.bellman_principle
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:12.876108+00:00
-- url     : https://prove2.me/theorems/b35fdcb9-a5b0-49a8-8f49-42e3997c96a5
-- title:
--   §B.1, §B.3 (unnumbered) — Bellman principle of optimality
-- statement:
--   Let $E$ be a separable real Banach space and assume (H1)–(H7). For $0\le t\le T$ and $\xi\in E$,
--   $$
--   V(t,\xi)=\inf\Bigl\{\int_t^T L(s,y(s),\dot y(s))\,ds+V(T,y(T))\Bigr\},
--   $$
--   the infimum over arcs $y\in W^{1,1}([t,T],E)$ with $\dot y(s)\in\Gamma(s,y(s))$ for a.e. $s\in[t,T]$ and $y(t)=\xi$.
--
--   The paper invokes the dynamic programming principle in the proofs of Theorems 3.1, 3.2 and 4.1 without stating it; both its uses, "$V(0,x_\theta(0))\le\int_0^tL+V(t,x_\theta(t))$" for an arc admissible only on $[0,t]$ (p.31) and "there is an admissible $x$ with $\int_t^TL+V(T,x(T))<V(t,\xi)+\varepsilon$" (p.25), are instances of this identity.
--
--   **Formalization Note** The infimum and the sum are in the extended reals.
--
--   Differences from the source:
--   - reading: the Bellman principle of optimality, invoked without statement → V(t, ξ) = inf over arcs y on [t, T] with ẏ ∈ Γ a.e. and y(t) = ξ of ∫_t^T L + V(T, y(T)), under (H1)–(H7), for 0 ≤ t ≤ T; reason: both uses in the paper (pp.25, 31) are instances; the infimum ranges over arcs on [t, T] because the p.31 arc is admissible only there
--   - encoding: functions on ℝ₊ = [0, ∞) → functions on ℝ with every condition restricted to [0, ∞) (derivatives and weak* derivatives at t > 0); reason: Lean convention; values at negative times are never used, same instances
--   - encoding: E* the norm dual; ẋ the strong derivative → E →L[ℝ] ℝ with the operator norm; deriv x; reason: Lean convention; same objects (deriv agrees with the strong derivative wherever it exists, which is a.e.)
--   - encoding: V : ℝ₊ × E → ℝ ∪ {±∞}, inf ∅ = +∞; improper integral as lim_{T→∞} ∫_t^T → EReal-valued valueFn (iInf, ⊤ for the empty family); the improper integral requires integrability on each [t, T] and an EReal limit; reason: Lean convention; integrability makes the finite integrals genuine and holds for every arc under (H2)–(H3)
--   - encoding: L : ℝ₊ × E × E → ℝ ∪ {+∞} → L : ℝ → E → E → ℝ; reason: (H3) bounds |L(t, 0, 0)| and makes L(t, ·, ·) Lipschitz, so L is finite everywhere
--   - encoding: there exist moduli l₁, l₂ (H3) and γ (H6) → l₁, l₂, γ as arguments with hypotheses HypH3, HypH6, HypH7 on the same functions; reason: a universally quantified hypothesis is equivalent to an existential one; the moduli are shared with (H7)
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, proof of Theorem 3.1, §B.1, pp.24–25, and proof of Theorem 4.1, §B.3, p.31, display "V(0, xθ(0)) ≤ ∫_0^t L(s, xθ(s), ẋθ(s))ds + V(t, xθ(t))" (Bellman principle of optimality)

import Mathlib
import Definitions.Def_InfHorizonVP_IsArcOn
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

/-- **Bellman principle of optimality (§B.1, §B.3).**
Frankowska, Sagara, arXiv:1801.00400v3, invoked without statement in the proof of Theorem 3.1
(§B.1, pp.24–25: "Then by (H1) and the Bellman principle of optimality, there exists x(·) ∈ 𝒜_(t,ξ)
such that ∫_t^T L(s, x(s), ẋ(s))ds + V(T, x(T)) < V(t, ξ) + ε") and of Theorem 4.1 (§B.3, p.31:
"By the Bellman principle of optimality, we have V(0, xθ(0)) ≤ ∫_0^t L(s, xθ(s), ẋθ(s))ds +
V(t, xθ(t))").

Under (H1)–(H7), for `0 ≤ t ≤ T` and `ξ ∈ E`,
`V(t, ξ) = inf {∫_t^T L(s, y(s), ẏ(s)) ds + V(T, y(T))}` over arcs `y ∈ W^{1,1}([t, T], E)` with
`ẏ(s) ∈ Γ(s, y(s))` a.e. on `[t, T]` and `y(t) = ξ`.

**Formalization Note.** Both uses on the page are instances: "≤" for an arc admissible only on
`[t, T]` (the p.31 display), and "≥ up to ε" for the restriction of an admissible trajectory. The
infimum and the sum are in `EReal`. -/
theorem bellman_principle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (L : ℝ → E → E → ℝ) (Γ : ℝ → E → Set E) (l₁ l₂ γ : ℝ → ℝ)
    (hH1 : HypH1 Γ) (hH2 : HypH2 L) (hH3 : HypH3 L l₁ l₂) (hH4 : HypH4 Γ) (hH5 : HypH5 Γ)
    (hH6 : HypH6 Γ γ) (hH7 : HypH7 l₁ l₂ γ)
    (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (ξ : E) :
    valueFn L Γ t ξ =
      ⨅ (y : ℝ → E) (_ : IsArcOn y t T ∧
          (∀ᵐ s ∂(volume.restrict (Icc t T)), deriv y s ∈ Γ s (y s)) ∧ y t = ξ),
        (((∫ s in t..T, L s (y s) (deriv y s)) : ℝ) : EReal) + valueFn L Γ T (y T) := by sorry

end InfHorizonVP
