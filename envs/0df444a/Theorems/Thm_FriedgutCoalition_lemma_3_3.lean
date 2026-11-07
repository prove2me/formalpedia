-- Prove2me | Theorems.Thm_FriedgutCoalition_lemma_3_3
-- name    : FriedgutCoalition.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:28.691058+00:00
-- url     : https://prove2.me/theorems/38f5b2a7-922d-4b8e-a74e-aad80b174d96
-- title:
--   Lemma 3.3 — direction switching: small influence towards $0$ gives a small coalition forcing $1$
-- statement:
--   For every $\varepsilon\in(0,1)$ there is a constant $C=C(\varepsilon)\ge1$ such that the following holds. For all $n,r\in\mathbb N$, $\tau>0$ and every monotone $f:[r]^n\to\{0,1\}$ with
--
--   $$\mathbb E_{x\sim U_n}[f(x)]\ge\varepsilon\qquad\text{and}\qquad\mathbf J^0(f)\le\tau,$$
--
--   there is $T\subseteq[n]$ with $|T|\le\exp(C\cdot\tau^2)$ and $\mathbf P^1_T(f)\ge1-\varepsilon$.
--
--   Here $U_n$ is the uniform distribution on $[r]^n$ and $\mathbf J^0(f)$ is the total influence towards $0$. The bound depends on neither $n$ nor $r$; this is the key lemma of the paper.
--
--   Differences from the source:
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
--   - encoding: r ∈ ℕ (an alphabet [r] = {1,…,r}) → any r : ℕ, including r = 0; reason: at r = 0 and n ≥ 1 the domain [0]ⁿ is empty and the lemma (its hypothesis E[f] ≥ ε > 0 fails) holds trivially; no instance with r ≥ 1 changes
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Lemma 3.3, p.8

import Mathlib
import Definitions.Def_FriedgutCoalition_coalProb

namespace FriedgutCoalition

/-- **Lemma 3.3** (direction switching; Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.8). For every
`ε ∈ (0,1)` there is `C = C(ε) ≥ 1` such that for all `n, r ∈ ℕ`, `τ > 0` and every monotone
`f : [r]ⁿ → {0,1}` with `E_{x∼Uₙ}[f(x)] ≥ ε` and `J⁰(f) ≤ τ` there is `T ⊆ [n]` with
`|T| ≤ exp(C · τ²)` and `P¹_T(f) ≥ 1 − ε`.

**Formalization Note.** `[r]ⁿ` is `Fin n → Fin r` with the uniform weights `unif r`; `exp` is the
natural exponential. No hypothesis on `r` is needed: at `r = 0`, `n ≥ 1` the hypothesis
`E[f] ≥ ε > 0` fails. `C` comes before `n`, `r`, `τ` and `f`. -/
theorem lemma_3_3 : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n r : ℕ) (τ : ℝ), 0 < τ → ∀ f : (Fin n → Fin r) → Bool, Monotone f →
      ε ≤ outProb (unif r) f true → totalToward (unif r) f false ≤ τ →
      ∃ T : Finset (Fin n), (T.card : ℝ) ≤ Real.exp (C * τ ^ 2) ∧
        1 - ε ≤ coalProb (unif r) f T true := by sorry

end FriedgutCoalition
