-- Prove2me | Theorems.Thm_FowlerLSQC_GateDistance_gateDist_phase_invariant
-- name    : FowlerLSQC.GateDistance.gateDist_phase_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:07.658568+00:00
-- url     : https://prove2.me/theorems/3b596828-b15c-4e2c-b163-b3b148eda277
-- title:
--   §10.1, p.110: the distance (10.1) ignores global phase
-- statement:
--   Let $m\ge 1$, let $U,V\in U(m)$, and let $\alpha,\beta$ be real numbers. Then
--
--   $$
--   \mathrm{dist}\left(e^{i\alpha}U,\ e^{i\beta}V\right)=\mathrm{dist}(U,V).
--   $$
--
--   This is the property for which Fowler prefers $\mathrm{dist}$ to the trace distance of the Solovay–Kitaev theorem: a gate and its phase-shifted copies are not distinguished, so an approximating sequence need not match an irrelevant phase.
--
--   **Formalization Note** The phase-shifted gate is `phaseShift α U`. The phases on the two arguments are independent.
--
--   Differences from the source:
--   - reading: the page says only that the trace distance "does not ignore global phase", by contrast with this metric → equality of $\mathrm{dist}$ under an independent phase on each argument; reason: this is the strongest reading of "ignores global phase", and a common phase on both arguments is the special case $\alpha=\beta$.
--   - encoding: $U(m)$, the $m$-dimensional unitary group → `Matrix.unitaryGroup (Fin m) ℂ` with `0 < m`; reason: the formula is $0/0$ at $m=0$, so the hypothesis only excludes an undefined case.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.1, p.110 (PDF 128)

import Mathlib
import Definitions.Def_FowlerLSQC_GateDistance_gateDist
import Definitions.Def_FowlerLSQC_GateDistance_phaseShift

namespace FowlerLSQC.GateDistance

/-- The distance (10.1) ignores global phase: for `m ≥ 1`, `U, V ∈ U(m)` and all real `α, β`,
`dist(e^{iα} U, e^{iβ} V) = dist(U, V)`. Fowler, *Towards Large-Scale Quantum Computation*,
arXiv:quant-ph/0506126v1, §10.1, p.110 (PDF 128): "This metric has been used in preference to the
trace distance used in the Solovay-Kitaev theorem [120, 30], as the trace distance does not ignore
global phase".

**Formalization Note** The page says this by contrast with the trace distance. It is read as an
equality for an independent phase on each argument. `0 < m` is the encoding of "m-dimensional". -/
theorem gateDist_phase_invariant {m : ℕ} (hm : 0 < m) (α β : ℝ)
    (U V : Matrix.unitaryGroup (Fin m) ℂ) :
    gateDist (phaseShift α U) (phaseShift β V) = gateDist U V := by sorry

end FowlerLSQC.GateDistance
