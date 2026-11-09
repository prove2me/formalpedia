-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_theorem_2_1
-- name    : MultiplierAssoc206.Resolution.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:09:25.876052+00:00
-- url     : https://prove2.me/theorems/29606092-9444-4e58-b5a4-69a5d226537b
-- title:
--   Size–width tradeoff of Ben-Sasson and Wigderson (corrected: width difference floored at 0)
-- statement:
--   Let $\Phi$ be an unsatisfiable CNF with $N$ variables, width $w(\Phi)$ and minimum refutation width $w(\Phi\vdash\bot)$. There is an absolute constant $c>0$ such that
--   $$\mathrm{size}_{\mathrm{Res}}(\Phi)\ \ge\ \exp\!\left(c\,\frac{\max\big(0,\,w(\Phi\vdash\bot)-w(\Phi)\big)^2}{N}\right).$$
--   In particular, for all constants $w_0$, $C_1$ and $c_2>0$ there are $c>0$ and $m_0$ such that for every $m\ge m_0$ and every unsatisfiable CNF $\Phi$ of width at most $w_0$ with at most $C_1m$ variables all of whose resolution refutations have width at least $c_2m$,
--   $$\mathrm{size}_{\mathrm{Res}}(\Phi)\ \ge\ 2^{cm}.$$
--
--   This is the tool that turns the width lower bound for the star-local extension into a size lower bound (Theorem 5.6).
--
--   **Formalization Note** The width difference is a truncated natural-number subtraction, which is the maximum with $0$. When $N=0$ the real quotient is $0$ and the bound reads $\mathrm{size}_{\mathrm{Res}}(\Phi)\ge1$.
--
--   Differences from the source:
--   - correction: size_Res(Φ) ≥ exp(Ω((w(Φ⊢⊥)−w(Φ))²/N)) for every unsatisfiable Φ → the exponent uses max(0, w(Φ⊢⊥)−w(Φ))² (natural-number subtraction); reason: the printed bound is false: Φ = x ∧ ¬x ∧ (y₁ ∨ … ∨ y_{N−1}) is unsatisfiable with N variables, size_Res(Φ) = 3, w(Φ⊢⊥) = 1 and w(Φ) = N−1, so exp(c(N−2)²/N) > 3 for large N whatever c > 0; every use in the paper has w(Φ⊢⊥) ≥ w(Φ), where the two agree
--   - encoding: Ω(·) and 'constant width, O(m) variables, width Ω(m), size 2^{Ω(m)}' → an absolute c > 0 chosen before Φ; for the particular case, for all w₀, C₁, c₂ > 0 there are c > 0 and m₀ with the bound for m ≥ m₀; reason: explicit form of the asymptotic notation; the constants depend only on the constants of the hypotheses
--   - encoding: N variables, with N ≥ 1 implicit → N = 0 allowed; the real quotient by 0 is 0 and the bound becomes size ≥ 1; reason: an unsatisfiable CNF without variables contains the empty clause and has a refutation of size 1, so no instance changes
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.5 (printed p.4), Theorem 2.1

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

namespace MultiplierAssoc206.Resolution

/-- Theorem 2.1 (size–width tradeoff, [BW01]), PDF p.5 (printed p.4), with the difference of
widths floored at `0` (corrected: the printed bound fails when `w(Φ) > w(Φ ⊢ ⊥)`), and its
"in particular" clause. -/
theorem theorem_2_1 :
    (∃ c : ℝ, 0 < c ∧ ∀ (α : Type) (Φ : CNF α), Unsatisfiable Φ →
      Real.exp (c * (((refWidth Φ - cnfWidth Φ : ℕ) : ℝ) ^ 2 / (numVars Φ : ℝ))) ≤
        (sizeRes Φ : ℝ)) ∧
    (∀ (w₀ : ℕ) (C₁ c₂ : ℝ), 0 < c₂ →
      ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (α : Type) (Φ : CNF α),
        Unsatisfiable Φ → cnfWidth Φ ≤ w₀ → (numVars Φ : ℝ) ≤ C₁ * m →
        (∀ π, IsRefutation Φ π → c₂ * m ≤ (derivWidth π : ℝ)) →
        (2 : ℝ) ^ (c * m) ≤ (sizeRes Φ : ℝ)) := by sorry

end MultiplierAssoc206.Resolution
