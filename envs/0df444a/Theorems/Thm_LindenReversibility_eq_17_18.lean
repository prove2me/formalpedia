-- Prove2me | Theorems.Thm_LindenReversibility_eq_17_18
-- name    : LindenReversibility.eq_17_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:25.89273+00:00
-- url     : https://prove2.me/theorems/25018c04-16bb-4601-8578-56fbb0f10c87
-- title:
--   Eqs. (17)–(18): a measurement by Bob or Claire does not increase Alice's entropy on average
-- statement:
--   Let $\psi$ be a unit vector of $\mathbb C^A\otimes\mathbb C^B\otimes\mathbb C^C$ and let Bob measure with a complete family $K_1,\dots,K_n$ on his system ($\sum_k K_k^\dagger K_k = I$). Let $\varphi_k = (I\otimes K_k\otimes I)\psi$, $p_k = \|\varphi_k\|^2$, $\psi_k = \varphi_k/\|\varphi_k\|$, and $\rho^A_k$ the reduced state of Alice in $\psi_k$. Then
--
--   1. (17) $\sum_k \operatorname{Tr}_{BC}|\varphi_k\rangle\langle\varphi_k| = \operatorname{Tr}_{BC}|\psi\rangle\langle\psi|$, i.e. $\rho^A = \sum_k p_k\rho^A_k$;
--   2. (18) $S(\rho^A) \ge \sum_k p_k S(\rho^A_k)$.
--
--   3–4. The same two statements hold when Claire measures, with $\varphi_k = (I\otimes I\otimes K_k)\psi$.
--
--   The paper derives (18) from (17) by "the convexity of entropy", i.e. concavity of the von Neumann entropy. With the invariance of $S$ under Alice's unitary (19) this gives (20).
--
--   Differences from the source:
--   - reading: the local Hilbert spaces of Alice, Bob and Claire "including ancilla's" (dimension not stated) → arbitrary finite index types A, B, C; reason: the paper works with density matrices, a min over separable states (11) and finitely many copies of finite-dimensional systems; arbitrary finite types cover any number of copies and any ancillas
--   - generalization: a local measurement with spectral projectors P_k (followed by outcome-dependent unitaries) → any finite family K_k of operators on the acting party's system with sum_k K_k^dagger K_k = 1; reason: spectral projectors, projectors followed by unitaries, and single unitaries are such families, so the statement specializes to the paper's; the paper's argument uses only the completeness relation
--   - encoding: Alice; Bob-Claire → the first tensor factor A of A × (B × C); the second factor B × C; reason: a labelling of the factors; the other pairs follow by relabelling the parties
--   - encoding: outcome probabilities p_k and normalized post-measurement states → p_k = ‖φ_k‖² for the unnormalized branch vector φ_k and the normalized branch φ_k/‖φ_k‖ (0 if φ_k = 0); reason: for a unit vector ψ these are the paper's p_k = Tr(P_k ⊗ I ⊗ I ρ^{ABC}) and states (7); a zero-probability outcome contributes 0 to every sum, as in the paper
--   - generalization: (17) and (18) for a measurement by Bob → clauses for Bob and for Claire; reason: Claire's clauses are Bob's with B and C exchanged; the paper's argument covers any party ("(15) is true for any step"); the Bob clauses are the source's statement
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eqs. (16)–(18), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_LindenReversibility_liftB
import Definitions.Def_LindenReversibility_liftC
import Definitions.Def_LindenReversibility_IsKrausFamily
import Definitions.Def_LindenReversibility_entA

open QAlgorithms (act traceRight pureDensity)
open scoped Matrix ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eqs. (17)–(18), p.3:
when Bob measures, before he communicates, Alice's average state is unchanged,
`ρ^A = ∑_k p_k ρ^A_k` (17), and therefore ("the convexity [concavity] of entropy")
`S(ρ^A) ≥ ∑_k p_k S(ρ^A_k)` (18). The same holds for a measurement by Claire.

Clauses 1–2 are (17) and (18) for Bob, clauses 3–4 for Claire.

**Formalization Note.** Alice is the first factor `A`; `ρ^A = Tr_{BC}` (`traceRight`). A
measurement is a complete family `K_k` (`IsKrausFamily`) on Bob's `B` (resp. Claire's `C`).
With `φ_k = (1 ⊗ K_k ⊗ 1) ψ`, (17) is stated for the unnormalized branches,
`Tr_{BC} |φ_k⟩⟨φ_k| = p_k ρ^A_k`; in (18), `p_k = ‖φ_k‖²` and `S(ρ^A_k)` is `entA` of the
normalized branch `φ_k / ‖φ_k‖`, in `ℝ≥0∞`. -/
theorem eq_17_18 {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (ψ : EuclideanSpace ℂ (A × (B × C))) (hψ : ‖ψ‖ = 1) :
    (∀ (n : ℕ) (K : Fin n → Matrix B B ℂ), IsKrausFamily K →
      ∑ k, traceRight (pureDensity (act (liftB (K k)) ψ)) = traceRight (pureDensity ψ)) ∧
    (∀ (n : ℕ) (K : Fin n → Matrix B B ℂ), IsKrausFamily K →
      ∑ k, ENNReal.ofReal (‖act (liftB (K k)) ψ‖ ^ 2) *
          entA ((‖act (liftB (K k)) ψ‖⁻¹ : ℝ) • act (liftB (K k)) ψ) ≤ entA ψ) ∧
    (∀ (n : ℕ) (K : Fin n → Matrix C C ℂ), IsKrausFamily K →
      ∑ k, traceRight (pureDensity (act (liftC (K k)) ψ)) = traceRight (pureDensity ψ)) ∧
    (∀ (n : ℕ) (K : Fin n → Matrix C C ℂ), IsKrausFamily K →
      ∑ k, ENNReal.ofReal (‖act (liftC (K k)) ψ‖ ^ 2) *
          entA ((‖act (liftC (K k)) ψ‖⁻¹ : ℝ) • act (liftC (K k)) ψ) ≤ entA ψ) := by sorry

end LindenReversibility
