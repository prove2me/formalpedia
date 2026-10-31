-- Prove2me | Theorems.Thm_OgawaNagaoka_eq18_power_mean
-- name    : OgawaNagaoka.eq18_power_mean
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:18.955439+00:00
-- url     : https://prove2.me/theorems/b577cf9f-69dc-4f74-99a5-87afe7c2fc77
-- title:
--   Eq. (18): $\sum_i\pi_iA_i\le(\sum_i\pi_iA_i^{1/\gamma})^\gamma$
-- statement:
--   Let $A_1,\dots,A_a\ge0$ be operators on a finite-dimensional Hilbert space, $\pi$ a probability distribution on $\{1,\dots,a\}$, and $0<\gamma\le1$. Then
--
--   $$
--   \sum_{i=1}^a\pi_iA_i\le\Big(\sum_{i=1}^a\pi_iA_i^{1/\gamma}\Big)^\gamma .
--   $$
--
--   It is the case $\beta=1$ of Lemma 4 and the step from which the general case follows by operator monotonicity.
--
--   Differences from the source:
--   - reading: $\pi$ (not specified in the statement) → `π ∈ stdSimplex ℝ ι`; reason: $\pi$ is the probability distribution of $f$ and $E_0$ throughout; the proof's dilation (19) uses $\sum_i\pi_i=1$
--   - encoding: index set $\{1,\dots,a\}$, operators $A_i\ge0$ on $H$ → finite type `ι`, positive semidefinite matrices over a finite type `D`; reason: the space is finite dimensional
--   - encoding: operator inequality $X\le Y$ → `(Y - X).PosSemidef`; reason: this is the definition of the Loewner order
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, eq. (18), p.8

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow

open scoped ComplexOrder

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, eq. (18), p.8 (proof of Lemma 4): for `0 < γ ≤ 1` and `A_i ≥ 0`,
`Σ_{i=1}^a π_i A_i ≤ (Σ_{i=1}^a π_i A_i^{1/γ})^γ`.

**Formalization Note.** `π` is a probability distribution on the finite index set (the `π` of
Lemma 4 and of `f`). `X ≤ Y` is `(Y - X).PosSemidef`; powers are `matPow`. -/
theorem eq18_power_mean {ι D : Type} [Fintype ι] [Fintype D] [DecidableEq D] (π : ι → ℝ)
    (hπ : π ∈ stdSimplex ℝ ι) (A : ι → Matrix D D ℂ) (hA : ∀ i, (A i).PosSemidef) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (matPow (∑ i, ((π i : ℝ) : ℂ) • matPow (A i) (1 / γ)) γ -
      ∑ i, ((π i : ℝ) : ℂ) • A i).PosSemidef := by sorry

end OgawaNagaoka
