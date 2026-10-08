-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_theorem_3_1
-- name    : HomogBiLimit.OutputFeedback.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:02.505313+00:00
-- url     : https://prove2.me/theorems/d9a9c744-8026-416e-9bf4-1d3c514a2913
-- title:
--   Theorem 3.1 — one step of the recursive observer design
-- statement:
--   Let $n\ge2$, let $\mathfrak d_0,\mathfrak d_\infty\in(-1,\frac1{n-1})$ and let $r_0,r_\infty$ be the weights (3.2). Let $1\le i<n$. Suppose $K_{i+1}:\mathbb R^{n-i}\to\mathbb R^{n-i}$ is a vector field homogeneous in the bi-limit with triples $((r_{0,i+1},\dots,r_{0,n}),\mathfrak d_0,K_{i+1,0})$ and $((r_{\infty,i+1},\dots,r_{\infty,n}),\mathfrak d_\infty,K_{i+1,\infty})$ such that the origin is globally asymptotically stable for
--   $$\dot E_{i+1}=S_{n-i}E_{i+1}+K_{i+1}(e_{i+1})\tag{3.5}$$
--   and for the same system with $K_{i+1,0}$ and with $K_{i+1,\infty}$ in place of $K_{i+1}$, where $E_{i+1}=(e_{i+1},\dots,e_n)$.
--   Then there is a vector field $K_i:\mathbb R^{n-i+1}\to\mathbb R^{n-i+1}$, homogeneous in the bi-limit with triples $((r_{0,i},\dots,r_{0,n}),\mathfrak d_0,K_{i,0})$ and $((r_{\infty,i},\dots,r_{\infty,n}),\mathfrak d_\infty,K_{i,\infty})$, such that the origin is globally asymptotically stable for
--   $$\dot E_i=S_{n-i+1}E_i+K_i(e_i),\qquad \dot E_i=S_{n-i+1}E_i+K_{i,0}(e_i),\qquad \dot E_i=S_{n-i+1}E_i+K_{i,\infty}(e_i).$$
--
--   This is the induction step of the observer design of §3: an output-injection gain for the last $n-i$ integrators is extended to one for the last $n-i+1$.
--
--   **Formalization Note** $K(e)$ for a scalar $e$ means $K(e,0,\dots,0)$ (footnote 6); the gain is a vector field on the whole space, and its homogeneity is that of the vector field. The paper's hypothesis "the origin is GAS for these systems" is read as GAS of (3.5) and of both approximations, which is what the paper's proof uses (it applies Theorem 2.20 to all three). Global asymptotic stability (GAS) of the origin of $\dot x=f(x)$ is the published notion `ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable` applied to the time-invariant field ($f(0)=0$, from every initial state there is a solution on $[0,\infty)$, Lyapunov stability and uniform global attractivity for *every* solution on $[0,\infty)$; solutions need not be unique, since the fields are only continuous), together with the requirement that no solution escapes to infinity in finite time, so that every solution is defined on $[0,\infty)$. For a continuous autonomous field this is the textbook notion of GAS (Bacciotti–Rosier, *Liapunov Functions and Stability in Control Theory*, §2; uniform attractivity follows from Kurzweil's converse theorem).
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, p. 11, Theorem 3.1 with the setting (3.5) and the standing assumptions of p. 10 ((3.2), degrees in (−1, 1/(n−1)))

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- Theorem 3.1 (homogeneous in the bi-limit observer design), p. 11. The index `i` is the
paper's (`1 ≤ i < n`); `K` is the paper's `K_{i+1} : ℝ^{n−i} → ℝ^{n−i}` with weights
`(r_{i+1},…,r_n)` of (3.2), and the conclusion's `K'` is `K_i : ℝ^{n−i+1} → ℝ^{n−i+1}` with
weights `(r_i,…,r_n)`. -/
theorem theorem_3_1 (n : ℕ) (hn : 2 ≤ n) (𝔡₀ 𝔡inf : ℝ)
    (h𝔡₀ : AdmissibleDegree n 𝔡₀) (h𝔡inf : AdmissibleDegree n 𝔡inf)
    (i : ℕ) (hi : 1 ≤ i) (hin : i < n)
    (K K₀ Kinf : (Fin (n - i) → ℝ) → (Fin (n - i) → ℝ))
    (hK : IsHomogBiLimitVF K (weights n 𝔡₀ i (n - i)) 𝔡₀ K₀
      (weights n 𝔡inf i (n - i)) 𝔡inf Kinf)
    (hgas : IsGAS (errorField K) ∧ IsGAS (errorField K₀) ∧ IsGAS (errorField Kinf)) :
    ∃ K' K'₀ K'inf : (Fin (n - i + 1) → ℝ) → (Fin (n - i + 1) → ℝ),
      IsHomogBiLimitVF K' (weights n 𝔡₀ (i - 1) (n - i + 1)) 𝔡₀ K'₀
        (weights n 𝔡inf (i - 1) (n - i + 1)) 𝔡inf K'inf ∧
      IsGAS (errorField K') ∧ IsGAS (errorField K'₀) ∧ IsGAS (errorField K'inf) := by sorry

end HomogBiLimit.OutputFeedback
