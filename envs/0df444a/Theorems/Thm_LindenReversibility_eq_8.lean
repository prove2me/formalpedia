-- Prove2me | Theorems.Thm_LindenReversibility_eq_8
-- name    : LindenReversibility.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:29.720715+00:00
-- url     : https://prove2.me/theorems/8d3b4cee-d2b4-4d8e-9e53-540d6c5bb8a7
-- title:
--   Eq. (8): Alice's measurement leaves $\rho^{BC}$ unchanged on average
-- statement:
--   Let $\psi$ be a unit vector in $\mathbb C^A\otimes\mathbb C^B\otimes\mathbb C^C$ (Alice, Bob, Claire; ancillas included), and let Alice measure with a complete family of operators $K_1,\dots,K_n$ on her system, $\sum_k K_k^\dagger K_k = I$. Write $\varphi_k = (K_k\otimes I\otimes I)\psi$ for the unnormalized branch after outcome $k$. Then
--
--   $$
--   \sum_k \operatorname{Tr}_A |\varphi_k\rangle\langle\varphi_k| = \operatorname{Tr}_A|\psi\rangle\langle\psi| .
--   $$
--
--   Since $\operatorname{Tr}_A|\varphi_k\rangle\langle\varphi_k| = p_k\,\rho^{BC}_k$ with $p_k = \|\varphi_k\|^2$ the probability of outcome $k$ and $\rho^{BC}_k$ Bob and Claire's state after it, this is the paper's $\rho^{BC} = \sum_k p_k\rho^{BC}_k$: before Alice communicates her outcome, Bob and Claire's average state has not changed. It is the input to Donald's identity (10) in the proof of (13).
--
--   Differences from the source:
--   - reading: the local Hilbert spaces of Alice, Bob and Claire "including ancilla's" (dimension not stated) → arbitrary finite index types A, B, C; reason: the paper works with density matrices, a min over separable states (11) and finitely many copies of finite-dimensional systems; arbitrary finite types cover any number of copies and any ancillas
--   - generalization: a local measurement with spectral projectors P_k (followed by outcome-dependent unitaries) → any finite family K_k of operators on the acting party's system with sum_k K_k^dagger K_k = 1; reason: spectral projectors, projectors followed by unitaries, and single unitaries are such families, so the statement specializes to the paper's; the paper's argument uses only the completeness relation
--   - encoding: Alice; Bob-Claire → the first tensor factor A of A × (B × C); the second factor B × C; reason: a labelling of the factors; the other pairs follow by relabelling the parties
--   - encoding: outcome probabilities p_k and normalized post-measurement states → p_k = ‖φ_k‖² for the unnormalized branch vector φ_k and the normalized branch φ_k/‖φ_k‖ (0 if φ_k = 0); reason: for a unit vector ψ these are the paper's p_k = Tr(P_k ⊗ I ⊗ I ρ^{ABC}) and states (7); a zero-probability outcome contributes 0 to every sum, as in the paper
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (8), p.2 (with eq. (7))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_LindenReversibility_liftA
import Definitions.Def_LindenReversibility_IsKrausFamily

open QAlgorithms (act traceLeft pureDensity)
open scoped Matrix

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eq. (8), p.2: after a
measurement by Alice, but before she communicates the outcome, the average state of Bob and
Claire is unchanged: `ρ^{BC} = ∑_k p_k ρ^{BC}_k`.

**Formalization Note.** Alice is the first factor `A` of `A × (B × C)`. Her measurement is a
complete family of operators `K_k` (`IsKrausFamily`; the paper's spectral projectors `P_k`
are one). The branch after outcome `k` is the unnormalized vector `φ_k = (K_k ⊗ 1 ⊗ 1) ψ`, so
`Tr_A |φ_k⟩⟨φ_k| = p_k ρ^{BC}_k` with `p_k = ‖φ_k‖²`; the identity is stated in this form. -/
theorem eq_8 {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (ψ : EuclideanSpace ℂ (A × (B × C))) (hψ : ‖ψ‖ = 1)
    {n : ℕ} (K : Fin n → Matrix A A ℂ) (hK : IsKrausFamily K) :
    ∑ k, traceLeft (pureDensity (act (liftA (K k)) ψ)) = traceLeft (pureDensity ψ) := by sorry

end LindenReversibility
