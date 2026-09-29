-- Prove2me | Theorems.Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re
-- name    : NumberField.dedekindZeta_ne_zero_of_one_lt_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/919658eb-d6a7-5910-a101-8c9a5d93643b
-- title:
--   Non-vanishing of ζ_K on Re(s)>1
-- statement:
--   Let $K$ be a field equipped with a number field structure (so $K$ is a finite extension of $\mathbb{Q}$), and let $s \in \mathbb{C}$ satisfy $\operatorname{Re}(s) > 1$. Then the value at $s$ of the Dedekind zeta function `NumberField.dedekindZeta K`, namely the $L$-series whose $n$-th coefficient is the number of nonzero ideals $\mathfrak{a}$ of the ring of integers $\mathcal{O}_K$ with absolute norm $N(\mathfrak{a}) = [\mathcal{O}_K : \mathfrak{a}] = n$, is nonzero: $\zeta_K(s) \ne 0$. Here $\zeta_K(s)$ denotes the sum of the Dirichlet series $\sum_{n \ge 1} \#\{\mathfrak{a} : N(\mathfrak{a}) = n\}\, n^{-s}$ itself, in the sense of Mathlib's `LSeries` (which assigns the value $0$ to a non-summable family), not the value of a meromorphic continuation; the hypothesis $\operatorname{Re}(s) > 1$ places $s$ in the half-plane of absolute convergence, where the series sum agrees with the classical analytic function. The conclusion is the non-vanishing statement only; no Euler product or growth estimate is asserted.
--
--   This is the classical non-vanishing of the Dedekind zeta function of a number field in its half-plane of absolute convergence, which follows from the Euler product expansion over the primes of $\mathcal{O}_K$. It is used in the analytic part of the project dealing with Eisenstein series and intertwining integrals, where the Dedekind zeta values occur as normalising factors in Bruhat-type Eisenstein continuations and must be inverted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re.lean

import Mathlib.NumberTheory.NumberField.DedekindZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.dedekindZeta_ne_zero_of_one_lt_re (K : Type*) [Field K]
    [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s ≠ 0 := by sorry
