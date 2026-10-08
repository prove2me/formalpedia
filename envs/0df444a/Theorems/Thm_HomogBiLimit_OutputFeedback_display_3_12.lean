-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_display_3_12
-- name    : HomogBiLimit.OutputFeedback.display_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:40.753884+00:00
-- url     : https://prove2.me/theorems/57ac73e4-f25a-42f8-a005-8385fcf4a3e2
-- title:
--   §3, display (3.12) — a homogeneous in the bi-limit observer for the chain of integrators
-- statement:
--   Let $n\ge2$, $\mathfrak d_0,\mathfrak d_\infty\in(-1,\frac1{n-1})$ and let $r_0,r_\infty$ be the weights (3.2). There is a vector field $K_1:\mathbb R^n\to\mathbb R^n$, homogeneous in the bi-limit with triples $(r_0,\mathfrak d_0,K_{1,0})$ and $(r_\infty,\mathfrak d_\infty,K_{1,\infty})$, such that the origin is globally asymptotically stable for
--   $$\dot E_1=S_nE_1+K_1(e_1),\qquad \dot E_1=S_nE_1+K_{1,0}(e_1),\qquad \dot E_1=S_nE_1+K_{1,\infty}(e_1).$$
--
--   These are the error dynamics of the observer (3.3), so $K_1$ yields a global observer for the chain of integrators that also works for its homogeneous approximations at the origin and at infinity.
--
--   **Formalization Note** $K_1(e_1)$ means $K_1(e_1,0,\dots,0)$ (footnote 6). Global asymptotic stability (GAS) of the origin of $\dot x=f(x)$ is the published notion `ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable` applied to the time-invariant field ($f(0)=0$, from every initial state there is a solution on $[0,\infty)$, Lyapunov stability and uniform global attractivity for *every* solution on $[0,\infty)$; solutions need not be unique, since the fields are only continuous), together with the requirement that no solution escapes to infinity in finite time, so that every solution is defined on $[0,\infty)$. For a continuous autonomous field this is the textbook notion of GAS (Bacciotti–Rosier, *Liapunov Functions and Stability in Control Theory*, §2; uniform attractivity follows from Kurzweil's converse theorem).
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, §3, display (3.12), pp. 14–15

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- §3, display (3.12), pp. 14–15: the recursive observer. For `n ≥ 2` and admissible degrees
there is a vector field `K₁ : ℝⁿ → ℝⁿ`, homogeneous in the bi-limit with triples
`(r₀, 𝔡₀, K_{1,0})` and `(r∞, 𝔡∞, K_{1,∞})` (weights (3.2)), such that the origin is
globally asymptotically stable for `Ė₁ = Sₙ E₁ + K₁(e₁)` and its two approximations. -/
theorem display_3_12 (n : ℕ) (hn : 2 ≤ n) (𝔡₀ 𝔡inf : ℝ)
    (h𝔡₀ : AdmissibleDegree n 𝔡₀) (h𝔡inf : AdmissibleDegree n 𝔡inf) :
    ∃ K K₀ Kinf : (Fin n → ℝ) → (Fin n → ℝ),
      IsHomogBiLimitVF K (weights n 𝔡₀ 0 n) 𝔡₀ K₀ (weights n 𝔡inf 0 n) 𝔡inf Kinf ∧
      IsGAS (errorField K) ∧ IsGAS (errorField K₀) ∧ IsGAS (errorField Kinf) := by sorry

end HomogBiLimit.OutputFeedback
