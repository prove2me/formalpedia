-- Prove2me | Theorems.Thm_FowlerLSQC_Canonical_nonlocalGate_local_conj
-- name    : FowlerLSQC.Canonical.nonlocalGate_local_conj
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:06.101879+00:00
-- url     : https://prove2.me/theorems/5e7fd8ab-249f-4954-adf9-07d6e94fa5c3
-- title:
--   Local conjugations permute and negate $\theta_1,\theta_2,\theta_3$ (4.25)–(4.30)
-- statement:
--   Let
--   $$
--   P_{12}=e^{i\pi/4\,Z}\otimes e^{i\pi/4\,Z},\quad P_{13}=e^{i\pi/4\,Y}\otimes e^{i\pi/4\,Y},\quad P_{23}=e^{i\pi/4\,X}\otimes e^{i\pi/4\,X},
--   $$
--   $$
--   M_{12}=e^{i\pi/4\,Z}\otimes e^{-i\pi/4\,Z},\quad M_{13}=e^{i\pi/4\,Y}\otimes e^{-i\pi/4\,Y},\quad M_{23}=e^{i\pi/4\,X}\otimes e^{-i\pi/4\,X}.
--   $$
--   Then for every $\vec\theta=(\theta_1,\theta_2,\theta_3)\in\mathbb R^3$:
--   1. $G_{(\theta_2,\theta_1,\theta_3)}=P_{12}G_{\vec\theta}P_{12}^\dagger$ (4.25);
--   2. $G_{(\theta_3,\theta_2,\theta_1)}=P_{13}G_{\vec\theta}P_{13}^\dagger$ (4.26);
--   3. $G_{(\theta_1,\theta_3,\theta_2)}=P_{23}G_{\vec\theta}P_{23}^\dagger$ (4.27);
--   4. $G_{(-\theta_2,-\theta_1,\theta_3)}=M_{12}G_{\vec\theta}M_{12}^\dagger$ (4.28);
--   5. $G_{(-\theta_3,\theta_2,-\theta_1)}=M_{13}G_{\vec\theta}M_{13}^\dagger$ (4.29);
--   6. $G_{(\theta_1,-\theta_3,-\theta_2)}=M_{23}G_{\vec\theta}M_{23}^\dagger$ (4.30).
--
--   Together with (4.16)–(4.18), these local equivalences are what allow any $\vec\theta$ to be moved into the region fixed by the uniqueness conditions.
--
--   **Formalization Note** $e^{it\sigma}$ is `singleQubitExp σ t` (matrix exponential), $P^\dagger$ is `Pᴴ`, and the six local gates are written out in the statement.
--
--   Differences from the source:
--   - encoding: $\theta_1,\theta_2,\theta_3$ → `θ 0, θ 1, θ 2`; $P_{ij}$, $M_{ij}$ written inline rather than named; reason: Lean convention, same instances.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.4, (4.19)–(4.30), pp.52–53 (PDF pp.70–71)

import Mathlib
import Definitions.Def_FowlerLSQC_Canonical_nonlocalGate
import Definitions.Def_FowlerLSQC_Canonical_singleQubitExp

open scoped Kronecker Matrix

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.4,
(4.19)–(4.30), pp.52–53 (PDF pp.70–71): with
`P12 = e^{iπ/4 Z} ⊗ e^{iπ/4 Z}`, `P13 = e^{iπ/4 Y} ⊗ e^{iπ/4 Y}`, `P23 = e^{iπ/4 X} ⊗ e^{iπ/4 X}`,
`M12 = e^{iπ/4 Z} ⊗ e^{−iπ/4 Z}`, `M13 = e^{iπ/4 Y} ⊗ e^{−iπ/4 Y}`, `M23 = e^{iπ/4 X} ⊗ e^{−iπ/4 X}`,
for every `θ ∈ ℝ³`:
`G_(θ2,θ1,θ3) = P12 G_θ P12†` (4.25), `G_(θ3,θ2,θ1) = P13 G_θ P13†` (4.26),
`G_(θ1,θ3,θ2) = P23 G_θ P23†` (4.27), `G_(−θ2,−θ1,θ3) = M12 G_θ M12†` (4.28),
`G_(−θ3,θ2,−θ1) = M13 G_θ M13†` (4.29), `G_(θ1,−θ3,−θ2) = M23 G_θ M23†` (4.30).

**Formalization Note.** `θ 0, θ 1, θ 2` are the book's `θ1, θ2, θ3`. `e^{itσ}` is
`singleQubitExp σ t` (matrix exponential); `P†` is `Pᴴ`. The `P`'s and `M`'s are written out in
the statement rather than named. -/
theorem nonlocalGate_local_conj (θ : Fin 3 → ℝ) :
    nonlocalGate ![θ 1, θ 0, θ 2] =
        (singleQubitExp QAlgorithms.pauliZ (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliZ (Real.pi / 4)) * nonlocalGate θ *
          (singleQubitExp QAlgorithms.pauliZ (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliZ (Real.pi / 4))ᴴ ∧
    nonlocalGate ![θ 2, θ 1, θ 0] =
        (singleQubitExp QAlgorithms.pauliY (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliY (Real.pi / 4)) * nonlocalGate θ *
          (singleQubitExp QAlgorithms.pauliY (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliY (Real.pi / 4))ᴴ ∧
    nonlocalGate ![θ 0, θ 2, θ 1] =
        (singleQubitExp QAlgorithms.pauliX (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliX (Real.pi / 4)) * nonlocalGate θ *
          (singleQubitExp QAlgorithms.pauliX (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliX (Real.pi / 4))ᴴ ∧
    nonlocalGate ![-θ 1, -θ 0, θ 2] =
        (singleQubitExp QAlgorithms.pauliZ (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliZ (-(Real.pi / 4))) * nonlocalGate θ *
          (singleQubitExp QAlgorithms.pauliZ (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliZ (-(Real.pi / 4)))ᴴ ∧
    nonlocalGate ![-θ 2, θ 1, -θ 0] =
        (singleQubitExp QAlgorithms.pauliY (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliY (-(Real.pi / 4))) * nonlocalGate θ *
          (singleQubitExp QAlgorithms.pauliY (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliY (-(Real.pi / 4)))ᴴ ∧
    nonlocalGate ![θ 0, -θ 2, -θ 1] =
        (singleQubitExp QAlgorithms.pauliX (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliX (-(Real.pi / 4))) * nonlocalGate θ *
          (singleQubitExp QAlgorithms.pauliX (Real.pi / 4) ⊗ₖ
            singleQubitExp QAlgorithms.pauliX (-(Real.pi / 4)))ᴴ := by sorry

end FowlerLSQC.Canonical
