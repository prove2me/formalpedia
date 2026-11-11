-- Prove2me | Theorems.Thm_LabelConnected_Treewidth_phi_factorization
-- name    : LabelConnected.Treewidth.phi_factorization
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:27:17.010435+00:00
-- url     : https://prove2.me/theorems/87abb98f-21af-421f-b384-b1451a688f58
-- title:
--   §6.1 compressing the partitions — Φ_U = Ψ_U Ψ_U^T over F_2, with 2^{h−1} commonly respected cuts
-- statement:
--   Let $U$ be a nonempty finite set and $u_0 \in U$. For partitions $\pi, \pi'$ of $U$ let $h$ be the number of blocks of $\pi \vee \pi'$. The number of cuts ($\kappa \subseteq U$ with $u_0 \in \kappa$) respected by both $\pi$ and $\pi'$ is $2^{h-1}$, and this number is odd precisely when $h = 1$; hence, over $\mathbb F_2$,
--   $$\Phi_U = \Psi_U \Psi_U^{\mathsf T}.$$
--
--   This rank-based factorization (Bodlaender, Cygan, Kratsch, Nederlof [10]) is what lets the dynamic program of Theorem 6.2 keep only a row basis of $\Psi$ for each signature, so that its tables stay single-exponential in the bag size.
--
--   Differences from the source:
--
--   - encoding: a nonempty set U, its partitions, π ∨ π′, matrices over F2 → a Fintype U with a given u₀ : U (so U is nonempty), Finpartition of Finset.univ, join via the equivalence closure, entries in ZMod 2; reason: Lean convention; same instances
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), p. 28, §6.1, Compressing the Partitions

import Mathlib
import Definitions.Def_LabelConnected_Treewidth_Partitions

open Classical

namespace LabelConnected.Treewidth

/-- **§6.1, Compressing the Partitions** (p. 28, from [10]). For a nonempty finite set `U` with a
fixed element `u₀`: for all partitions `π, π′` of `U`, the number of cuts respected by both `π` and
`π′` is `2^{h−1}`, where `h` is the number of blocks of `π ∨ π′`, and this number is odd precisely
when `h = 1`; and `Φ_U = Ψ_U Ψ_Uᵀ` over `𝔽₂`. -/
theorem phi_factorization {U : Type} [Fintype U] [DecidableEq U] (u₀ : U) :
    (∀ π π' : UPartition U,
      (Finset.univ.filter fun κ : Cut u₀ => Respects π κ.1 ∧ Respects π' κ.1).card =
          2 ^ ((join π π').parts.card - 1) ∧
        (Odd (Finset.univ.filter fun κ : Cut u₀ => Respects π κ.1 ∧ Respects π' κ.1).card ↔
          (join π π').parts.card = 1)) ∧
    Phi U = Psi u₀ * (Psi u₀).transpose := by sorry

end LabelConnected.Treewidth
