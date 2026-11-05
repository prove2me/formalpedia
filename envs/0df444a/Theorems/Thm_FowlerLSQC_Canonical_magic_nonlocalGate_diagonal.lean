-- Prove2me | Theorems.Thm_FowlerLSQC_Canonical_magic_nonlocalGate_diagonal
-- name    : FowlerLSQC.Canonical.magic_nonlocalGate_diagonal
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:05.375446+00:00
-- url     : https://prove2.me/theorems/75685042-50c4-4500-bb19-907561351c03
-- title:
--   $Q^\dagger G_{\vec\theta}Q$ is diagonal (4.8)
-- statement:
--   For every $\vec\theta=(\theta_1,\theta_2,\theta_3)\in\mathbb R^3$, the purely non-local gate $G_{\vec\theta}=e^{i(\theta_1X\otimes X+\theta_2Y\otimes Y+\theta_3Z\otimes Z)}$ is diagonal in the magic basis:
--   $$
--   \tilde G_{\vec\theta}=Q^\dagger G_{\vec\theta}Q=\mathrm{diag}\big(e^{i(\theta_1-\theta_2+\theta_3)},\ e^{i(-\theta_1+\theta_2+\theta_3)},\ e^{-i(\theta_1+\theta_2+\theta_3)},\ e^{i(\theta_1+\theta_2-\theta_3)}\big),
--   $$
--   with the diagonal in the order $|\Phi_1\rangle,\dots,|\Phi_4\rangle$ of the columns of $Q$.
--
--   This is what lets the construction read off $\vec\theta$ from the eigenphases $\epsilon_k$ of the magic-basis matrix.
--
--   **Formalization Note** `θ 0, θ 1, θ 2` are $\theta_1,\theta_2,\theta_3$; the diagonal is indexed by `Fin 4`.
--
--   Differences from the source:
--   - encoding: $\theta_1,\theta_2,\theta_3$ and the magic basis indexed from $1$ → indexed from $0$ (`Fin 3`, `Fin 4`); reason: Lean convention, same instances.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.3, (4.8), p.51 (PDF p.69)

import Mathlib
import Definitions.Def_FowlerLSQC_Canonical_magicQ
import Definitions.Def_FowlerLSQC_Canonical_nonlocalGate
open scoped Matrix

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.3, (4.8),
p.51 (PDF p.69): in the magic basis the non-local gate is diagonal,
`G̃_θ = Q† G_θ Q = diag(e^{i(θ1−θ2+θ3)}, e^{i(−θ1+θ2+θ3)}, e^{−i(θ1+θ2+θ3)}, e^{i(θ1+θ2−θ3)})`,
for every `θ ∈ ℝ³`.

**Formalization Note.** `θ 0, θ 1, θ 2` are the book's `θ1, θ2, θ3`; the diagonal is indexed by
`Fin 4` in the order `Φ1, …, Φ4` of the columns of `Q` ((4.3)). `Q†` is `magicQᴴ`. -/
theorem magic_nonlocalGate_diagonal (θ : Fin 3 → ℝ) :
    magicQᴴ * nonlocalGate θ * magicQ =
      Matrix.diagonal ![Complex.exp (Complex.I * ((θ 0 : ℂ) - θ 1 + θ 2)),
        Complex.exp (Complex.I * (-(θ 0 : ℂ) + θ 1 + θ 2)),
        Complex.exp (-(Complex.I * ((θ 0 : ℂ) + θ 1 + θ 2))),
        Complex.exp (Complex.I * ((θ 0 : ℂ) + θ 1 - θ 2))] := by sorry

end FowlerLSQC.Canonical
