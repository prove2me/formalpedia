-- Prove2me | Theorems.Thm_KnillLaflammeQEC_isKrausFamily_of_projections
-- name    : KnillLaflammeQEC.isKrausFamily_of_projections
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:18.058177+00:00
-- url     : https://prove2.me/theorems/dfe66062-25ac-4467-a95b-9c9221406c6c
-- title:
--   Eqs. (22)–(23), p.14 — orthogonal projections followed by unitaries form a superoperator
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space, $\{P_r\}_{r\in K}$ a finite family of orthogonal projections on $\mathcal H$ ($P_r^\dagger=P_r$, $P_r^2=P_r$) that together span the Hilbert space, in the sense $\sum_r P_r=I$, and $\{W_r\}$ unitary operators on $\mathcal H$. Then the operators $W_rP_r$ satisfy the superoperator condition
--
--   $$
--   \sum_r (W_rP_r)^\dagger (W_rP_r)=I .
--   $$
--
--   In the proof of Theorem 3.2 this shows that the recovery $\mathcal R=\{\mathcal O,R_1,\dots,R_r,\dots\}$ of Eqs.(22)–(23) is a superoperator: the projections are $\mathcal O$ and $\sum_i|\nu^i_r\rangle\langle\nu^i_r|$, followed by $I$ and the unitaries $V_r$.
--
--   Differences from the source:
--   - encoding: an $n$-dimensional Hilbert space $\mathcal H$ and linear operators on it → `EuclideanSpace ℂ ι` for a finite type `ι`, operators `Matrix ι ι ℂ` acting by `QAlgorithms.act`; reason: Lean convention; every $n$-dimensional Hilbert space is isometric to $\mathbb C^n$, so the instances are the same
--   - reading: "orthogonal projections … where the projections span the Hilbert space" → `(P r)ᴴ = P r ∧ P r * P r = P r` for each `r`, and `∑ r, P r = 1`; reason: in the paper's recovery the projections have mutually orthogonal ranges ($\mathcal O$ and the $\sum_i|\nu^i_r\rangle\langle\nu^i_r|$), and mutually orthogonal projections span $\mathcal H$ exactly when they sum to $I$; without mutual orthogonality the claim is false ($P_1=P_2=I$)
--   - generalization: the specific recovery $\mathcal R=\{\mathcal O,R_1,\dots\}$ of (22)–(23) → any finite family of projections `P : K → Matrix ι ι ℂ` and unitaries `W : K → Matrix.unitaryGroup ι ℂ`; reason: the paper's sentence is this general observation; $P=(\mathcal O,\sum_i|\nu^i_r\rangle\langle\nu^i_r|)$, $W=(I,V_r)$ gives the recovery
-- source:
--   Knill, Laflamme, A Theory of Quantum Error-Correcting Codes, arXiv:quant-ph/9604034v1, proof of Theorem 3.2, Eqs.(22)–(23), p.14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
open scoped Matrix

namespace KnillLaflammeQEC

/-- Knill, Laflamme, *A Theory of Quantum Error-Correcting Codes*, arXiv:quant-ph/9604034v1,
proof of Theorem 3.2, p.14, after Eqs.(22)–(23): "That `R` is a superoperator follows from the
observation that it is a sum of orthogonal projections followed by unitary operators where the
projections span the Hilbert space." If `P_r` are orthogonal projections (`P_r† = P_r`,
`P_r² = P_r`) with `Σ_r P_r = I` and `W_r` are unitaries, then `{W_r P_r}` satisfies
`Σ_r (W_r P_r)† (W_r P_r) = I` (Eq.(5)).

**Formalization Note.** Operators are matrices `Matrix ι ι ℂ`, unitaries are elements of
`Matrix.unitaryGroup ι ℂ`, the index set `K` is finite, and the superoperator condition is
`QAlgorithms.IsKrausFamily`. In the paper the projections are `O` (with `W = I`) and
`Σ_i |ν^i_r⟩⟨ν^i_r|` (with `W = V_r`). -/
theorem isKrausFamily_of_projections {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (P : K → Matrix ι ι ℂ) (hP : ∀ r, (P r)ᴴ = P r ∧ P r * P r = P r) (hsum : ∑ r, P r = 1)
    (W : K → Matrix.unitaryGroup ι ℂ) :
    QAlgorithms.IsKrausFamily (fun r => (W r : Matrix ι ι ℂ) * P r) := by sorry

end KnillLaflammeQEC
