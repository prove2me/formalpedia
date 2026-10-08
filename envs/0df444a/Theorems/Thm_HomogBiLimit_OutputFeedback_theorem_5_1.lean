-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_theorem_5_1
-- name    : HomogBiLimit.OutputFeedback.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:51.160327+00:00
-- url     : https://prove2.me/theorems/6ca3021c-a9a6-436e-a858-4e5de6a8ade9
-- title:
--   Theorem 5.1 — global stabilization of a chain of integrators by a homogeneous in the bi-limit output feedback, for every gain $L>0$
-- statement:
--   Consider the chain of integrators with output $y=x_1$,
--   $$\dot x=S_nx+B_nu,\qquad y=x_1,\tag{5.1}$$
--   with $x\in\mathbb R^n$, $u\in\mathbb R$, and the output feedback with observer state $\hat{\mathfrak X}_n\in\mathbb R^n$
--   $$\dot{\hat{\mathfrak X}}_n=L\bigl(S_n\hat{\mathfrak X}_n+B_n\phi_n(\hat{\mathfrak X}_n)+K_1(x_1-\hat x_1)\bigr),\qquad u=L^n\phi_n(\hat{\mathfrak X}_n).\tag{5.2}$$
--
--   **Theorem.** Let $n\ge2$ and $\mathfrak d_0,\mathfrak d_\infty\in(-1,\frac1{n-1})$, and let $r_0,r_\infty$ be the weights (3.2). There exist a function $\phi_n:\mathbb R^n\to\mathbb R$, homogeneous in the bi-limit with triples $(r_0,1+\mathfrak d_0,\phi_{n,0})$ and $(r_\infty,1+\mathfrak d_\infty,\phi_{n,\infty})$, and a vector field $K_1:\mathbb R^n\to\mathbb R^n$, homogeneous in the bi-limit with triples $(r_0,\mathfrak d_0,K_{1,0})$ and $(r_\infty,\mathfrak d_\infty,K_{1,\infty})$, such that **for every** $L>0$ the origin of $\mathbb R^{2n}$ is a globally asymptotically stable equilibrium of the closed loop (5.1)–(5.2), and also of the closed loops obtained by replacing $(\phi_n,K_1)$ with $(\phi_{n,0},K_{1,0})$ and with $(\phi_{n,\infty},K_{1,\infty})$.
--
--   The feedback and gain are chosen once, before $L$; the same pair works for every gain. This is the paper's main result: a single output feedback that is simultaneously a global stabilizer and has prescribed homogeneous behaviour near the origin and at infinity.
--
--   **Formalization Note** The closed loop lives on $\mathbb R^{2n}$ (`Fin (n + n) → ℝ`), with $x$ in the first $n$ and $\hat{\mathfrak X}_n$ in the last $n$ coordinates. $K_1(s)$ for a scalar $s$ means $K_1(s,0,\dots,0)$ (footnote 6). The argument $x_1-\hat x_1$ is kept as printed in (5.2), although the paper's (3.3) and (5.9) use $\hat x_1-x_1$; because $K_1$ is existentially quantified (replace $K_1$ by $E\mapsto K_1(-E)$), both versions are equivalent. Global asymptotic stability (GAS) of the origin of $\dot x=f(x)$ is the published notion `ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable` applied to the time-invariant field ($f(0)=0$, from every initial state there is a solution on $[0,\infty)$, Lyapunov stability and uniform global attractivity for *every* solution on $[0,\infty)$; solutions need not be unique, since the fields are only continuous), together with the requirement that no solution escapes to infinity in finite time, so that every solution is defined on $[0,\infty)$. For a continuous autonomous field this is the textbook notion of GAS (Bacciotti–Rosier, *Liapunov Functions and Stability in Control Theory*, §2; uniform attractivity follows from Kurzweil's converse theorem).
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, p. 20, Theorem 5.1 with (5.1), (5.2); proof §5.2, pp. 23–24

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- Theorem 5.1, p. 20 (goal): global asymptotic stabilization of the chain of integrators
(5.1) by the homogeneous in the bi-limit output feedback (5.2), for every gain `L > 0`. -/
theorem theorem_5_1 (n : ℕ) (hn : 2 ≤ n) (𝔡₀ 𝔡inf : ℝ)
    (h𝔡₀ : AdmissibleDegree n 𝔡₀) (h𝔡inf : AdmissibleDegree n 𝔡inf) :
    ∃ (φ φ₀ φinf : (Fin n → ℝ) → ℝ) (K K₀ Kinf : (Fin n → ℝ) → (Fin n → ℝ)),
      IsHomogBiLimit φ (weights n 𝔡₀ 0 n) (1 + 𝔡₀) φ₀ (weights n 𝔡inf 0 n) (1 + 𝔡inf) φinf ∧
      IsHomogBiLimitVF K (weights n 𝔡₀ 0 n) 𝔡₀ K₀ (weights n 𝔡inf 0 n) 𝔡inf Kinf ∧
      ∀ L : ℝ, 0 < L →
        IsGAS (closedLoop n φ K L) ∧ IsGAS (closedLoop n φ₀ K₀ L) ∧
          IsGAS (closedLoop n φinf Kinf L) := by sorry

end HomogBiLimit.OutputFeedback
