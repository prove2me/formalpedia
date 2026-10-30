-- Prove2me | Theorems.Thm_LindenReversibility_eq_22
-- name    : LindenReversibility.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:46.581039+00:00
-- url     : https://prove2.me/theorems/245ae682-639b-4576-844e-283df9bc8134
-- title:
--   Eq. (22): under any local protocol, the average gain in Bob–Claire $E_r$ is at most the average loss of Alice's entropy
-- statement:
--   Let Alice, Bob and Claire hold finite-dimensional systems (all copies and ancillas included) $\mathbb C^A$, $\mathbb C^B$, $\mathbb C^C$, and let them start from any pure state, a unit vector $\psi\in\mathbb C^A\otimes\mathbb C^B\otimes\mathbb C^C$. Let $P$ be any local protocol: a finite tree of rounds in which any party applies a complete family of measurement operators $\{K_k\}$ ($\sum_k K_k^\dagger K_k = I$) on their own system, announces the outcome, and the protocol continues depending on all outcomes so far. Each final branch is a pure state with a probability. Write $\langle\cdot\rangle_{\text{final}}$ for the probability-weighted average over the final branches, $E_r(BC)$ for the relative entropy of entanglement of Bob and Claire's reduced state and $S(A)$ for the von Neumann entropy of Alice's reduced state (natural logarithms). Then
--
--   $$
--   \langle E_r(BC)\rangle_{\text{final}} - E_r(BC)_{\text{initial}} \le S(A)_{\text{initial}} - \langle S(A)\rangle_{\text{final}} .
--   $$
--
--   Any increase of the bipartite entanglement between Bob and Claire must be paid for by a decrease of Alice's entanglement with them. In a reversible process the right-hand side vanishes, so the average relative entropy of entanglement of any pair of parties is conserved, which is how the paper shows that GHZ states cannot be converted reversibly into singlets.
--
--   Differences from the source:
--   - reading: the local Hilbert spaces of Alice, Bob and Claire "including ancilla's" (dimension not stated) → arbitrary finite index types A, B, C (B, C nonempty); reason: the paper works with density matrices, a min over separable states (11) and finitely many copies of finite-dimensional systems; arbitrary finite types cover any number of copies and any ancillas
--   - generalization: a local measurement with spectral projectors P_k (followed by outcome-dependent unitaries) → any finite family K_k of operators on the acting party's system with sum_k K_k^dagger K_k = 1; reason: spectral projectors, projectors followed by unitaries, and single unitaries are such families, so the statement specializes to the paper's; the paper's argument uses only the completeness relation
--   - encoding: Alice; Bob-Claire → the first tensor factor A of A × (B × C); the second factor B × C; reason: a labelling of the factors; the other pairs follow by relabelling the parties
--   - encoding: (22) as a difference of real quantities → the additive rearrangement in [0, +∞] (ℝ≥0∞); reason: every term is finite (nonnegative entropies; E_r is finite on states), so the rearranged inequality is equivalent
--   - encoding: min over separable σ in (11) → infimum over separable σ; reason: the minimum is attained (compact separable set, lower semicontinuous relative entropy), so the values agree
--   - encoding: probabilities and post-measurement states along the branches → unnormalized branch vectors φ, with probability ‖φ‖² and state φ/‖φ‖ (Protocol.avg); reason: for a unit initial vector and a local protocol, ‖φ‖² is the product of the outcome probabilities along the branch; zero-probability branches contribute 0
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (22), p.4 (introduced at the foot of p.3)

import Mathlib
import Definitions.Def_LindenReversibility_Protocol
import Definitions.Def_LindenReversibility_Protocol_IsLocal
import Definitions.Def_LindenReversibility_Protocol_avg
import Definitions.Def_LindenReversibility_entA
import Definitions.Def_LindenReversibility_erBC

open scoped ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eq. (22), p.4 (with
the sentence introducing it at the foot of p.3): "for any local protocol, the average increase in
E_r for the Bob-Claire system is no greater than the average decrease in the Alice's entanglement
with the joint Bob-Claire system", i.e.
`⟨E_r(BC)⟩_final − E_r(BC)_initial ≤ S(A)_initial − ⟨S(A)⟩_final`.

**Formalization Note.** The three parties' systems, "including ancilla's" (p.2), are arbitrary
finite index types `A`, `B`, `C` (`B`, `C` nonempty), so any number of copies and any
ancillas are covered; Alice is the first factor of `A × (B × C)`. The initial state is any unit
vector `ψ`. `P` is any finite protocol tree in which any party may act at any round with a
complete family of measurement operators (`Protocol.IsLocal`), later steps depending on all
earlier outcomes. `⟨·⟩_final` is `Protocol.avg`, the probability-weighted average over the
final pure branches. `E_r` (`erBC`) and `S(A)` (`entA`) use natural logarithms. (22) is stated
in `ℝ≥0∞` in the additive form `⟨E_r⟩_f + ⟨S(A)⟩_f ≤ E_r,i + S(A)_i` (all four terms are
finite). -/
theorem eq_22 {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (ψ : EuclideanSpace ℂ (A × (B × C))) (hψ : ‖ψ‖ = 1)
    (P : Protocol A B C) (hP : P.IsLocal) :
    P.avg erBC ψ + P.avg entA ψ ≤ erBC ψ + entA ψ := by sorry

end LindenReversibility
