-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_display_4_9
-- name    : HomogBiLimit.OutputFeedback.display_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:17.983974+00:00
-- url     : https://prove2.me/theorems/6cfa9bdc-4793-4dea-a4ce-f7b067a3633f
-- title:
--   §4, display (4.9) — a homogeneous in the bi-limit globally stabilizing state feedback
-- statement:
--   Let $n\ge2$, $\mathfrak d_0,\mathfrak d_\infty\in(-1,\frac1{n-1})$ and let $r_0,r_\infty$ be the weights (3.2). There is a function $\phi_n:\mathbb R^n\to\mathbb R$, homogeneous in the bi-limit with triples $(r_0,\mathfrak d_0+1,\phi_{n,0})$ and $(r_\infty,\mathfrak d_\infty+1,\phi_{n,\infty})$, such that the origin is globally asymptotically stable for
--   $$\dot{\mathfrak X}_n=S_n\mathfrak X_n+B_n\phi_n(\mathfrak X_n),\qquad \dot{\mathfrak X}_n=S_n\mathfrak X_n+B_n\phi_{n,0}(\mathfrak X_n),\qquad \dot{\mathfrak X}_n=S_n\mathfrak X_n+B_n\phi_{n,\infty}(\mathfrak X_n).$$
--
--   $\phi_n$ is the state feedback that the output feedback of Theorem 5.1 evaluates at the observer's estimate.
--
--   **Formalization Note** The degree is $\mathfrak d_0+r_{0,n}$ with $r_{0,n}=1$. (4.9) is printed without the time derivative dots. Global asymptotic stability (GAS) of the origin of $\dot x=f(x)$ is the published notion `ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable` applied to the time-invariant field ($f(0)=0$, from every initial state there is a solution on $[0,\infty)$, Lyapunov stability and uniform global attractivity for *every* solution on $[0,\infty)$; solutions need not be unique, since the fields are only continuous), together with the requirement that no solution escapes to infinity in finite time, so that every solution is defined on $[0,\infty)$. For a continuous autonomous field this is the textbook notion of GAS (Bacciotti–Rosier, *Liapunov Functions and Stability in Control Theory*, §2; uniform attractivity follows from Kurzweil's converse theorem).
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, §4, display (4.9), p. 19

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- §4, display (4.9), p. 19: the recursive state feedback. For `n ≥ 2` and admissible degrees
there is `φₙ : ℝⁿ → ℝ`, homogeneous in the bi-limit with triples `(r₀, 𝔡₀ + 1, φ_{n,0})` and
`(r∞, 𝔡∞ + 1, φ_{n,∞})` (weights (3.2), `r_{0,n} = r_{∞,n} = 1`), such that the origin is
globally asymptotically stable for `𝔛̇ₙ = Sₙ 𝔛ₙ + Bₙ φₙ(𝔛ₙ)` and its two approximations. -/
theorem display_4_9 (n : ℕ) (hn : 2 ≤ n) (𝔡₀ 𝔡inf : ℝ)
    (h𝔡₀ : AdmissibleDegree n 𝔡₀) (h𝔡inf : AdmissibleDegree n 𝔡inf) :
    ∃ φ φ₀ φinf : (Fin n → ℝ) → ℝ,
      IsHomogBiLimit φ (weights n 𝔡₀ 0 n) (𝔡₀ + 1) φ₀ (weights n 𝔡inf 0 n) (𝔡inf + 1) φinf ∧
      IsGAS (feedbackField φ) ∧ IsGAS (feedbackField φ₀) ∧ IsGAS (feedbackField φinf) := by sorry

end HomogBiLimit.OutputFeedback
