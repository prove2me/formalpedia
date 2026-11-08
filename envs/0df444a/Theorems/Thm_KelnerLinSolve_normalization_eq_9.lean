-- Prove2me | Theorems.Thm_KelnerLinSolve_normalization_eq_9
-- name    : KelnerLinSolve.normalization_eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:00.007617+00:00
-- url     : https://prove2.me/theorems/4187adbe-d618-45ba-8d13-83ddd8535b50
-- title:
--   §4.1, (9) — normalization: $\tfrac12\le\max|(A_0)_{ij}|<1$, $\kappa_2(A_0)=\kappa_2(A)$, and residual transfer
-- statement:
--   Take a well-formed instance of Theorem 1.1 with $n\ge1$, $A$ nonsingular and $b\neq0$. Let $\alpha,\beta$ be the maxima of $e+\mathrm{len}(u)$ over the nonzero entries $u2^e$ of $A$ and of $b$, and put $A_0 = 2^{-\alpha}A$, $b_0 = 2^{-\beta}b$. Then
--
--   $$
--   \tfrac12\le\max_{i,j}|(A_0)_{ij}|<1,\qquad \tfrac12\le\|b_0\|_\infty<1,\qquad \kappa_2(A_0)=\kappa_2(A),
--   $$
--
--   and for every vector $w$
--
--   $$
--   A(2^{\beta-\alpha}w)-b = 2^\beta(A_0w-b_0),\qquad \|b\|_2 = 2^\beta\|b_0\|_2. \tag{9}
--   $$
--
--   Consequently, if $\|A_0w-b_0\|_2\le\varepsilon\|b_0\|_2$ then $\|A(2^{\beta-\alpha}w)-b\|_2\le\varepsilon\|b\|_2$.
--
--   The normalized system meets the hypotheses of Lemma 3.4, and any relative-residual guarantee for it transfers unchanged to the original system.
--
--   Differences from the source:
--   - encoding: maxima of e + len(u) over the nonzero entries → `alphaExp`, `betaExp` (list maxima); reason: same values when A ≠ 0 and b ≠ 0, which hold here
--   - encoding: a relative-residual guarantee transfers unchanged → an implication for every w and every ε; reason: the page's sentence, made explicit
--   - encoding: the standing setting of §4.1 (Theorem 1.1 with b ≠ 0) → hypotheses `WellFormed`, 1 ≤ n, det A ≠ 0, b ≠ 0; reason: the page assumes them; 1 ≤ n excludes the empty system
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §4.1, p.12, Equation (9)

import Mathlib
import Definitions.Def_KelnerLinSolve_FloatInstance
import Definitions.Def_KelnerLinSolve_kappa2

open Matrix

namespace KelnerLinSolve

/-- **§4.1, normalization and Equation (9)**, Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit
Operations*, STOC 2027 submission (sha256 d1af55cb…), p.12. "Let `α` and `β` be the maxima of
`e + len(u)` over the nonzero entries of `A` and `b`, respectively, and define `A₀ = 2^{−α}A`,
`b₀ = 2^{−β}b`. … It gives `1/2 ≤ max_{i,j} |(A₀)_{ij}| < 1`, `1/2 ≤ ‖b₀‖_∞ < 1`,
`κ₂(A₀) = κ₂(A)`. … Moreover, for every vector `w`, `A(2^{β−α}w) − b = 2^β(A₀w − b₀)`,
`‖b‖₂ = 2^β‖b₀‖₂`. (9) Consequently, a relative-residual guarantee for the normalized system
transfers unchanged to the original system."

In the setting of Theorem 1.1 (a well-formed instance, `n ≥ 1`, `A` nonsingular) with `b ≠ 0`
("henceforth assume `b ≠ 0`", p.12): both displayed bounds, the equality of condition numbers, both
identities (9), and the transfer of a relative-residual bound `‖A₀w − b₀‖₂ ≤ ε‖b₀‖₂` to
`‖A(2^{β−α}w) − b‖₂ ≤ ε‖b‖₂`.

**Formalization Note.** `α = alphaExp I`, `β = betaExp I` (maxima over the listed entries,
respectively over the coordinates of `b` with nonzero significand); powers `2^{−α}` are `zpow`. -/
theorem normalization_eq_9 (I : FloatInstance) (hI : I.WellFormed) (hn : 1 ≤ I.n)
    (hdet : I.A.det ≠ 0) (hb : I.b ≠ 0) :
    let α : ℤ := I.alphaExp
    let β : ℤ := I.betaExp
    let A₀ : Matrix (Fin I.n) (Fin I.n) ℝ := (2 : ℝ) ^ (-α) • I.A
    let b₀ : Fin I.n → ℝ := (2 : ℝ) ^ (-β) • I.b
    (1 / 2 ≤ maxAbsEntry A₀ ∧ maxAbsEntry A₀ < 1) ∧
    (1 / 2 ≤ infNorm b₀ ∧ infNorm b₀ < 1) ∧
    kappa2 A₀ = kappa2 I.A ∧
    (∀ w : Fin I.n → ℝ, I.A *ᵥ ((2 : ℝ) ^ (β - α) • w) - I.b = (2 : ℝ) ^ β • (A₀ *ᵥ w - b₀)) ∧
    norm2 I.b = (2 : ℝ) ^ β * norm2 b₀ ∧
    (∀ (w : Fin I.n → ℝ) (ε : ℝ), norm2 (A₀ *ᵥ w - b₀) ≤ ε * norm2 b₀ →
      norm2 (I.A *ᵥ ((2 : ℝ) ^ (β - α) • w) - I.b) ≤ ε * norm2 I.b) := by sorry

end KelnerLinSolve
