-- Prove2me | Theorems.Thm_OgawaNagaoka_lemma4_power_monotone
-- name    : OgawaNagaoka.lemma4_power_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:23.711385+00:00
-- url     : https://prove2.me/theorems/47a319a5-34fc-421b-b4fb-acb2406a79c3
-- title:
--   Lemma 4: $(\sum_i\pi_iA_i^{1/\alpha})^\alpha\ge(\sum_i\pi_iA_i^{1/\beta})^\beta$ for $0<\alpha\le\beta\le1$
-- statement:
--   Let $A_1,\dots,A_a$ be non-negative bounded operators on the finite-dimensional Hilbert space $H$ and $\pi$ a probability distribution on $\{1,\dots,a\}$. If $0<\alpha\le\beta\le1$, then
--
--   $$
--   \Big(\sum_{i=1}^a\pi_iA_i^{1/\alpha}\Big)^\alpha\ge\Big(\sum_{i=1}^a\pi_iA_i^{1/\beta}\Big)^\beta .
--   $$
--
--   Taking traces with $A_i=\rho_i$ shows that $E_0(s,\pi)$ is non-decreasing in $s\in(-1,0]$, which gives (14) and (15).
--
--   Differences from the source:
--   - encoding: non-negative bounded operators on $H$ ($\dim H<\infty$, p.1) → positive semidefinite matrices over a finite type `D`; reason: the paper's standing assumption $\dim H<\infty$
--   - reading: $\pi$ (not specified in the statement) → `π ∈ stdSimplex ℝ ι`; reason: $\pi$ is the probability distribution of $f$ and $E_0$ throughout, and (18) and its proof use $\sum_i\pi_i=1$
--   - encoding: operator inequality $X\le Y$ → `(Y - X).PosSemidef`; reason: this is the definition of the Loewner order
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, Lemma 4, eq. (17), p.7

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow

open scoped ComplexOrder

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, Lemma 4, eq. (17), p.7: let `A_i` (`i = 1, …, a`) be non-negative bounded
operators in `H`. If `0 < α ≤ β ≤ 1` then
`(Σ_{i=1}^a π_i A_i^{1/α})^α ≥ (Σ_{i=1}^a π_i A_i^{1/β})^β`.

**Formalization Note.** `H` is finite dimensional (the paper's standing assumption, p.1), so the
`A_i` are positive semidefinite matrices. `π` is a probability distribution on the index set (the
`π` of `f` and `E₀`). `X ≥ Y` is `(X - Y).PosSemidef`; powers are `matPow`. -/
theorem lemma4_power_monotone {ι D : Type} [Fintype ι] [Fintype D] [DecidableEq D] (π : ι → ℝ)
    (hπ : π ∈ stdSimplex ℝ ι) (A : ι → Matrix D D ℂ) (hA : ∀ i, (A i).PosSemidef) (α β : ℝ)
    (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    (matPow (∑ i, ((π i : ℝ) : ℂ) • matPow (A i) (1 / α)) α -
      matPow (∑ i, ((π i : ℝ) : ℂ) • matPow (A i) (1 / β)) β).PosSemidef := by sorry

end OgawaNagaoka
