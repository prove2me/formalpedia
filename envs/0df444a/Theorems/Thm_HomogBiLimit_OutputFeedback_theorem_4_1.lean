-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_theorem_4_1
-- name    : HomogBiLimit.OutputFeedback.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:36.919741+00:00
-- url     : https://prove2.me/theorems/a943ac95-5c95-411c-8991-0c4786c278d9
-- title:
--   Theorem 4.1 — one step of the homogeneous in the bi-limit backstepping
-- statement:
--   Let $n\ge2$, $\mathfrak d_0,\mathfrak d_\infty\in(-1,\frac1{n-1})$, let $r_0,r_\infty$ be the weights (3.2), and let $1\le i<n$. Suppose there are $\phi_i:\mathbb R^i\to\mathbb R$, homogeneous in the bi-limit with triples $((r_{0,1},\dots,r_{0,i}),\mathfrak d_0+r_{0,i},\phi_{i,0})$ and $((r_{\infty,1},\dots,r_{\infty,i}),\mathfrak d_\infty+r_{\infty,i},\phi_{i,\infty})$, and $\alpha_i\ge1$ such that
--
--   1. $\psi_i=\phi_i^{\alpha_i}$ (signed power, $w^\alpha=\operatorname{sign}(w)|w|^\alpha$) is $C^1$, and for each $j\le i$ the function $\partial\psi_i/\partial x_j$ is homogeneous in the bi-limit with weights $(r_{0,1},\dots,r_{0,i})$, $(r_{\infty,1},\dots,r_{\infty,i})$, degrees $\alpha_i(r_{0,i}+\mathfrak d_0)-r_{0,j}$, $\alpha_i(r_{\infty,i}+\mathfrak d_\infty)-r_{\infty,j}$ and approximating functions $\partial\psi_{i,0}/\partial x_j$, $\partial\psi_{i,\infty}/\partial x_j$ for some $C^1$ functions $\psi_{i,0},\psi_{i,\infty}$;
--   2. the origin is globally asymptotically stable for $\dot{\mathfrak X}_i=S_i\mathfrak X_i+B_i\phi_i(\mathfrak X_i)$ and for the same system with $\phi_{i,0}$ and with $\phi_{i,\infty}$.
--
--   Then there are $\phi_{i+1}:\mathbb R^{i+1}\to\mathbb R$, homogeneous in the bi-limit with triples $((r_{0,1},\dots,r_{0,i+1}),\mathfrak d_0+r_{0,i+1},\phi_{i+1,0})$ and $((r_{\infty,1},\dots,r_{\infty,i+1}),\mathfrak d_\infty+r_{\infty,i+1},\phi_{i+1,\infty})$, and $\alpha_{i+1}>1$, with the same two properties for $i+1$.
--
--   This is the induction step of the backstepping design of §4.
--
--   **Formalization Note** Both sides are expressed with the predicate `BacksteppingProps` of the definition file. The paper leaves $\psi_{i0},\psi_{i\infty}$ implicit; they are quantified existentially as $C^1$ functions. The strict inequality $\alpha_{i+1}>1$ of the conclusion is kept as printed. (4.4) is printed without the time derivative dot; it is read as $\dot{\mathfrak X}_{i+1}$. Global asymptotic stability (GAS) of the origin of $\dot x=f(x)$ is the published notion `ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable` applied to the time-invariant field ($f(0)=0$, from every initial state there is a solution on $[0,\infty)$, Lyapunov stability and uniform global attractivity for *every* solution on $[0,\infty)$; solutions need not be unique, since the fields are only continuous), together with the requirement that no solution escapes to infinity in finite time, so that every solution is defined on $[0,\infty)$. For a continuous autonomous field this is the textbook notion of GAS (Bacciotti–Rosier, *Liapunov Functions and Stability in Control Theory*, §2; uniform attractivity follows from Kurzweil's converse theorem).
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, p. 16, Theorem 4.1 with the setting (4.1), (4.2) and the weights (3.2)

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- Theorem 4.1 (homogeneous in the bi-limit backstepping), p. 16. For `1 ≤ i < n`: if some
`φ_i : ℝ^i → ℝ` with some `α_i ≥ 1` has the properties of the theorem
(`BacksteppingProps`), then some `φ_{i+1} : ℝ^{i+1} → ℝ` with some `α_{i+1} > 1` has them. -/
theorem theorem_4_1 (n : ℕ) (hn : 2 ≤ n) (𝔡₀ 𝔡inf : ℝ)
    (h𝔡₀ : AdmissibleDegree n 𝔡₀) (h𝔡inf : AdmissibleDegree n 𝔡inf)
    (i : ℕ) (hi : 1 ≤ i) (hin : i < n)
    (h : ∃ (φ φ₀ φinf : (Fin i → ℝ) → ℝ) (α : ℝ), 1 ≤ α ∧
      BacksteppingProps n 𝔡₀ 𝔡inf i φ φ₀ φinf α) :
    ∃ (φ φ₀ φinf : (Fin (i + 1) → ℝ) → ℝ) (α : ℝ), 1 < α ∧
      BacksteppingProps n 𝔡₀ 𝔡inf (i + 1) φ φ₀ φinf α := by sorry

end HomogBiLimit.OutputFeedback
