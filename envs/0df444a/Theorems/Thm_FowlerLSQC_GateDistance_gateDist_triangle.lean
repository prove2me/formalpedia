-- Prove2me | Theorems.Thm_FowlerLSQC_GateDistance_gateDist_triangle
-- name    : FowlerLSQC.GateDistance.gateDist_triangle
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:37:04.725003+00:00
-- url     : https://prove2.me/theorems/51f75886-c5ff-410e-a546-f8e2bf2568ed
-- title:
--   §10.1, (10.2), p.110: triangle inequality for the gate distance on $U(m)$
-- statement:
--   Let $m\ge 1$ and $U,V,W\in U(m)$. The gate distance $\mathrm{dist}(U,V)=\sqrt{(m-|\mathrm{tr}(U^\dagger V)|)/m}$ satisfies the triangle inequality
--
--   $$
--   \mathrm{dist}(U,W)\le\mathrm{dist}(U,V)+\mathrm{dist}(V,W).
--   $$
--
--   Fowler gives this as the reason for the square root in (10.1). The inequality makes approximation errors along a sequence of gates add up under this distance, even though the distance vanishes on pairs of gates that differ only by a global phase.
--
--   Differences from the source:
--   - encoding: $U(m)$, the $m$-dimensional unitary group → `Matrix.unitaryGroup (Fin m) ℂ` with `0 < m`; reason: the formula is $0/0$ at $m=0$, so the hypothesis only excludes an undefined case.
--   - reading: $U,V,W$ are not quantified in (10.2) → all $U,V,W\in U(m)$, for every $m\ge 1$; reason: the section fixes $U(m)$ for general $m$ at its first sentence, and this is the strongest reading of the unquantified inequality.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.1, (10.2), p.110 (PDF 128)

import Mathlib
import Definitions.Def_FowlerLSQC_GateDistance_gateDist

namespace FowlerLSQC.GateDistance

/-- The triangle inequality (10.2) for the gate distance (10.1): for `m ≥ 1` and `U, V, W ∈ U(m)`,
`dist(U, W) ≤ dist(U, V) + dist(V, W)`. Fowler, *Towards Large-Scale Quantum Computation*,
arXiv:quant-ph/0506126v1, §10.1, (10.2), p.110 (PDF 128).

**Formalization Note** `0 < m` is the encoding of "m-dimensional": (10.1) is 0/0 at `m = 0`. Every
dimension is covered, not only the single-qubit case `m = 2` that the later sections use. -/
theorem gateDist_triangle {m : ℕ} (hm : 0 < m) (U V W : Matrix.unitaryGroup (Fin m) ℂ) :
    gateDist U W ≤ gateDist U V + gateDist V W := by sorry

end FowlerLSQC.GateDistance
