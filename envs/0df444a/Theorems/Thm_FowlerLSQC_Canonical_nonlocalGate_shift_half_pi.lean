-- Prove2me | Theorems.Thm_FowlerLSQC_Canonical_nonlocalGate_shift_half_pi
-- name    : FowlerLSQC.Canonical.nonlocalGate_shift_half_pi
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:04.551772+00:00
-- url     : https://prove2.me/theorems/5bd700ce-cd34-483a-912c-8eaf5c2d7131
-- title:
--   Shifting $\theta_k$ by $\pm\pi/2$ multiplies $G_{\vec\theta}$ by $\pm i\,\sigma\otimes\sigma$ (4.16)–(4.18)
-- statement:
--   For every $\vec\theta=(\theta_1,\theta_2,\theta_3)\in\mathbb R^3$ and each choice of sign,
--   $$
--   G_{(\theta_1\pm\pi/2,\theta_2,\theta_3)}=\pm i\,(X\otimes X)\,G_{(\theta_1,\theta_2,\theta_3)},
--   $$
--   $$
--   G_{(\theta_1,\theta_2\pm\pi/2,\theta_3)}=\pm i\,(Y\otimes Y)\,G_{(\theta_1,\theta_2,\theta_3)},
--   $$
--   $$
--   G_{(\theta_1,\theta_2,\theta_3\pm\pi/2)}=\pm i\,(Z\otimes Z)\,G_{(\theta_1,\theta_2,\theta_3)}.
--   $$
--   Since $\pm i$ is a global phase and $X\otimes X$, $Y\otimes Y$, $Z\otimes Z$ are local gates, each $\theta_k$ is determined only modulo $\pi/2$ by the local-equivalence class of the gate.
--
--   **Formalization Note** The statement is the conjunction of the six identities, sign $+$ then $-$ for each of (4.16), (4.17), (4.18).
--
--   Differences from the source:
--   - encoding: $\theta_1,\theta_2,\theta_3$ → `θ 0, θ 1, θ 2`; the $\pm$ of each display → two conjuncts; reason: Lean convention, same instances.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.4, (4.16)–(4.18), p.52 (PDF p.70)

import Mathlib
import Definitions.Def_FowlerLSQC_Canonical_nonlocalGate

open scoped Kronecker

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.4,
(4.16)–(4.18), p.52 (PDF p.70): for every `θ ∈ ℝ³` and both signs,
`G_(θ1±π/2,θ2,θ3) = ±i(X⊗X)G_θ`, `G_(θ1,θ2±π/2,θ3) = ±i(Y⊗Y)G_θ`,
`G_(θ1,θ2,θ3±π/2) = ±i(Z⊗Z)G_θ`.

**Formalization Note.** `θ 0, θ 1, θ 2` are the book's `θ1, θ2, θ3`; the six identities are the
six conjuncts (sign `+` then `−` for each of (4.16), (4.17), (4.18)). -/
theorem nonlocalGate_shift_half_pi (θ : Fin 3 → ℝ) :
    nonlocalGate ![θ 0 + Real.pi / 2, θ 1, θ 2] =
        Complex.I • ((QAlgorithms.pauliX ⊗ₖ QAlgorithms.pauliX) * nonlocalGate θ) ∧
    nonlocalGate ![θ 0 - Real.pi / 2, θ 1, θ 2] =
        (-Complex.I) • ((QAlgorithms.pauliX ⊗ₖ QAlgorithms.pauliX) * nonlocalGate θ) ∧
    nonlocalGate ![θ 0, θ 1 + Real.pi / 2, θ 2] =
        Complex.I • ((QAlgorithms.pauliY ⊗ₖ QAlgorithms.pauliY) * nonlocalGate θ) ∧
    nonlocalGate ![θ 0, θ 1 - Real.pi / 2, θ 2] =
        (-Complex.I) • ((QAlgorithms.pauliY ⊗ₖ QAlgorithms.pauliY) * nonlocalGate θ) ∧
    nonlocalGate ![θ 0, θ 1, θ 2 + Real.pi / 2] =
        Complex.I • ((QAlgorithms.pauliZ ⊗ₖ QAlgorithms.pauliZ) * nonlocalGate θ) ∧
    nonlocalGate ![θ 0, θ 1, θ 2 - Real.pi / 2] =
        (-Complex.I) • ((QAlgorithms.pauliZ ⊗ₖ QAlgorithms.pauliZ) * nonlocalGate θ) := by sorry

end FowlerLSQC.Canonical
