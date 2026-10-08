-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_eq_6_15
-- name    : MeanFieldPDE.Classical.eq_6_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:25.250086+00:00
-- url     : https://prove2.me/theorems/b02de39f-2fe9-4d8e-902a-532482d55aca
-- title:
--   (6.15), proof of Theorem 6.2, p. 35 — V(s, X^{t,x,P_ξ}_s, P_{X^{t,ξ}_s}) = E[Φ(X^{t,x,P_ξ}_T, P_{X^{t,ξ}_T}) | F_s]
-- statement:
--   Assume the coefficients are Lipschitz and $\Phi\in C^{2,1}_b(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$. For $0\le t\le s\le T$, $x\in\mathbb R^d$ and $\xi\in L^2(\mathcal F_t;\mathbb R^d)$,
--   $$V\big(s,X_s^{t,x,P_\xi},P_{X_s^{t,\xi}}\big)=E\big[\Phi(X_T^{t,x,P_\xi},P_{X_T^{t,\xi}})\,\big|\,\mathcal F_s\big]\quad P\text{-a.s.};$$
--   in particular $s\mapsto V(s,X_s^{t,x,P_\xi},P_{X_s^{t,\xi}})$ is a martingale on $[t,T]$.
--
--   The martingale property, combined with the Itô formula, forces the drift of $V$ along the dynamics to vanish, which is the PDE.
--
--   **Formalization Note** The hypotheses are those the identity needs (Lipschitz coefficients and the terminal function of the main theorem); (H.2) is not assumed. The conditional expectation is Mathlib's `condExp` with respect to $\mathcal F_s$ of the standing filtration.
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 35, (6.15), proof of Theorem 6.2

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- (6.15), proof of Theorem 6.2, p. 35: for `0 ≤ t ≤ s ≤ T`, `x ∈ ℝ^d` and `ξ ∈ L²(F_t; ℝ^d)`,
`V(s, X^{t,x,P_ξ}_s, P_{X^{t,ξ}_s}) = E[Φ(X^{t,x,P_ξ}_T, P_{X^{t,ξ}_T}) | F_s]` almost surely; in particular
`s ↦ V(s, X^{t,x,P_ξ}_s, P_{X^{t,ξ}_s})` is a martingale on `[t, T]`. -/
theorem eq_6_15 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b)
    (Φ : E d → Measure (E d) → ℝ) (hΦ : IsC21b P Φ)
    (Xξ : ℝ≥0 → (Ω → E d) → ℝ≥0 → Ω → E d)
    (Xx : ℝ≥0 → E d → (Ω → E d) → ℝ≥0 → Ω → E d)
    (hXξ : IsMVFamily hS σ b Xξ) (hXx : IsDecFamily hS σ b Xξ Xx) :
    ∀ t s : ℝ≥0, t ≤ s → s ≤ T → ∀ (x : E d) (ξ : Ω → E d), IsL2At hS t ξ →
      (fun ω => valueFn F₀ P T Φ Xξ Xx s (Xx t x ξ s ω) (P.map (Xξ t ξ s)))
        =ᵐ[P] P[fun ω => Φ (Xx t x ξ T ω) (P.map (Xξ t ξ T)) | filt hS s] := by sorry

end MeanFieldPDE.Classical
