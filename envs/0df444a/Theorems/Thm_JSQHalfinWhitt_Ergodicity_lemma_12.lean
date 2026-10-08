-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Ergodicity_lemma_12
-- name    : JSQHalfinWhitt.Ergodicity.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:51.035182+00:00
-- url     : https://prove2.me/theorems/e643fbb8-dd99-4b68-98e5-b64d29b38eb5
-- title:
--   Lemma 12 — f^{(2)} is well-defined on Ω, belongs to C²(Ω), and has the partials (C.8)–(C.9)
-- statement:
--   Fix an integer $n\ge1$ and $0<\beta<\kappa_1<\kappa_2$, let $\phi=\phi^{(\kappa_1/\sqrt n,\kappa_2/\sqrt n)}$, let $S_0,\dots,S_3$ be the regions of $\Omega$ cut out by the line $\{x_2=\kappa_1/\sqrt n\}$ and the curves $\Gamma^{(\kappa_1)}$, $\Gamma^{(\kappa_2)}$, and let $f^{(2)}$ be the six-case function of Lemma 12 (see the definition file), built from $\tau=\tau(x)$. Then:
--
--   1. $f^{(2)}$ is well defined on $\Omega$: its six regions cover $\Omega$, $\tau(x)<\infty$ on $S_2\cup S_3$, where the formulas use $\tau$, and two formulas agree wherever their regions overlap;
--   2. $f^{(2)}\in C^2(\Omega)$;
--   3. (C.8) its first partial in $x_1$ is
--   $$f^{(2)}_1(x)=\begin{cases}0,& x\in S_0\cup S_1,\\ \frac{\sqrt n}{\beta}\phi(x_2e^{-\tau(x)})e^{-\tau(x)},& x\in S_2,\\ \frac{\sqrt n}{\beta}e^{-\tau(x)},& x\in S_3;\end{cases}$$
--   4. (C.9) its first partial in $x_2$ is
--   $$f^{(2)}_2(x)=\begin{cases}0,& x\in S_0,\\ \frac{1}{x_2}\phi(x_2),& x\in S_1,\\ \frac{1}{x_2}\big(\phi(x_2)-\phi(x_2e^{-\tau(x)})\big)+\phi(x_2e^{-\tau(x)})\frac{\sqrt n}{\beta}e^{-\tau(x)}(\tau(x)+1),& x\in S_2,\\ \frac{\sqrt n}{\beta}e^{-\tau(x)}(\tau(x)+1),& x\in S_3.\end{cases}$$
--
--   $f^{(2)}$ is the solution of the second PDE (5.10) used in Lemma 8; (C.8)–(C.9) give the PDE, the reflection condition and the bounds (5.14), (5.16).
--
--   **Formalization Note** "Well-defined" is made explicit as the three clauses of item 1. The finiteness of $\tau$ on $S_2\cup S_3$ is part of it because the formulas use the real value of $\tau$ (`tauReal`), whose junk value $0$ at $\tau=\infty$ is therefore never reached. The partials are one-sided partials on $\Omega$, and (C.8)–(C.9) are asserted on each closed region $S_k$.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), pp. 41–42, Lemma 12, (C.8)–(C.9); S_0–S_3 on p. 41; standing assumptions on p. 35

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Ergodicity_Candidates

namespace JSQHalfinWhitt.Ergodicity

/-- Lemma 12, pp. 41–42. Let `n ≥ 1`, `0 < β < κ₁ < κ₂` and `φ = φ^{(κ₁/√n, κ₂/√n)}`.
`f^{(2)}` is well-defined on `Ω`: the six regions of its definition cover `Ω`, `τ(x) < ∞` on
`S₂ ∪ S₃` (where its formulas use `τ`), and two formulas agree wherever their regions overlap.
It belongs to `C²(Ω)`, and its partial derivatives are (C.8)
`f^{(2)}₁ = 0, 0, (√n/β)φ(x₂e^{−τ})e^{−τ}, (√n/β)e^{−τ}` on `S₀, S₁, S₂, S₃`, and (C.9)
`f^{(2)}₂ = 0, φ(x₂)/x₂, (φ(x₂) − φ(x₂e^{−τ}))/x₂ + φ(x₂e^{−τ})(√n/β)e^{−τ}(τ + 1),
(√n/β)e^{−τ}(τ + 1)` on `S₀, S₁, S₂, S₃`. -/
theorem lemma_12 (n : ℕ) (hn : 0 < n) (β κ1 κ2 : ℝ) (hβ : 0 < β) (hκ1 : β < κ1)
    (hκ12 : κ1 < κ2) :
    -- well-defined
    ((∀ x ∈ JSQHalfinWhitt.Tightness.Omega, ∃ k : Fin 6, x ∈ f2Region n β κ1 κ2 k) ∧
      (∀ x ∈ S2 n β κ1 κ2 ∪ S3 n β κ2, tau n β x ≠ ⊤) ∧
      (∀ (k k' : Fin 6) (x : ℝ × ℝ), x ∈ f2Region n β κ1 κ2 k → x ∈ f2Region n β κ1 κ2 k' →
        f2Branch n β κ1 κ2 k x = f2Branch n β κ1 κ2 k' x)) ∧
    ContDiffOn ℝ 2 (f2 n β κ1 κ2) JSQHalfinWhitt.Tightness.Omega ∧
    -- (C.8)
    (∀ x ∈ S0 n κ1, d1 (f2 n β κ1 κ2) x = 0) ∧
    (∀ x ∈ S1 n β κ1, d1 (f2 n β κ1 κ2) x = 0) ∧
    (∀ x ∈ S2 n β κ1 κ2, d1 (f2 n β κ1 κ2) x =
      Real.sqrt n / β * phiK n κ1 κ2 (x.2 * Real.exp (-tauReal n β x)) *
        Real.exp (-tauReal n β x)) ∧
    (∀ x ∈ S3 n β κ2, d1 (f2 n β κ1 κ2) x = Real.sqrt n / β * Real.exp (-tauReal n β x)) ∧
    -- (C.9)
    (∀ x ∈ S0 n κ1, d2 (f2 n β κ1 κ2) x = 0) ∧
    (∀ x ∈ S1 n β κ1, d2 (f2 n β κ1 κ2) x = 1 / x.2 * phiK n κ1 κ2 x.2) ∧
    (∀ x ∈ S2 n β κ1 κ2, d2 (f2 n β κ1 κ2) x =
      1 / x.2 * (phiK n κ1 κ2 x.2 - phiK n κ1 κ2 (x.2 * Real.exp (-tauReal n β x))) +
        phiK n κ1 κ2 (x.2 * Real.exp (-tauReal n β x)) * (Real.sqrt n / β) *
          Real.exp (-tauReal n β x) * (tauReal n β x + 1)) ∧
    (∀ x ∈ S3 n β κ2, d2 (f2 n β κ1 κ2) x =
      Real.sqrt n / β * Real.exp (-tauReal n β x) * (tauReal n β x + 1)) := by sorry

end JSQHalfinWhitt.Ergodicity
