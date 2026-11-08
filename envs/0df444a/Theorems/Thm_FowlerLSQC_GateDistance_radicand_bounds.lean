-- Prove2me | Theorems.Thm_FowlerLSQC_GateDistance_radicand_bounds
-- name    : FowlerLSQC.GateDistance.radicand_bounds
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:36:27.649736+00:00
-- url     : https://prove2.me/theorems/916ffd07-2bad-4306-892b-162bf753550f
-- title:
--   §10.1, p.110: the radicand of (10.1) lies between 0 and 1
-- statement:
--   Let $m\ge 1$ and $U,V\in U(m)$. Then
--
--   $$
--   0\le\frac{m-\left|\mathrm{tr}(U^\dagger V)\right|}{m}\le 1 .
--   $$
--
--   Equivalently, $|\mathrm{tr}(U^\dagger V)|\le m$, together with the trivial bound $|\mathrm{tr}(U^\dagger V)|\ge 0$.
--
--   This is what makes the square root in the definition of $\mathrm{dist}$ a genuine square root, so that the distance takes values in $[0,1]$.
--
--   **Formalization Note** The radicand is written out in full, exactly as it appears in the definition of `gateDist`. In Lean, `Real.sqrt` of a negative number is $0$, so the lower bound is what makes the definition the book's.
--
--   Differences from the source:
--   - encoding: $U(m)$, the $m$-dimensional unitary group → `Matrix.unitaryGroup (Fin m) ℂ` with `0 < m`; reason: the formula is $0/0$ at $m=0$, so the hypothesis only excludes an undefined case.
--   - reading: the page has $U_l$, a gate sequence in $U(m)$, as second argument → any $V\in U(m)$; reason: (10.1) defines a function on $U(m)$ and (10.2) applies it to arbitrary arguments.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.1, p.110 (PDF 128)

import Mathlib

open scoped Matrix

namespace FowlerLSQC.GateDistance

/-- The radicand of (10.1) lies between 0 and 1: for `m ≥ 1` and `U, V ∈ U(m)`,
`0 ≤ (m − |tr(U†V)|) / m ≤ 1`. Fowler, *Towards Large-Scale Quantum Computation*,
arXiv:quant-ph/0506126v1, §10.1, p.110 (PDF 128): "By subtracting this absolute value from m and
dividing by m a number between 0 and 1 is obtained."

**Formalization Note** The radicand is written out, exactly as in the definition of `gateDist`.
`0 < m` is the encoding of "m-dimensional": (10.1) is 0/0 at `m = 0`. -/
theorem radicand_bounds {m : ℕ} (hm : 0 < m) (U V : Matrix.unitaryGroup (Fin m) ℂ) :
    0 ≤ ((m : ℝ) - ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)).trace‖) /
        (m : ℝ) ∧
      ((m : ℝ) - ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)).trace‖) /
        (m : ℝ) ≤ 1 := by sorry

end FowlerLSQC.GateDistance
