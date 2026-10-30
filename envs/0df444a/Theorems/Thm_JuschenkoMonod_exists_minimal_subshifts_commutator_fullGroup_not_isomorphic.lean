-- Prove2me | Theorems.Thm_JuschenkoMonod_exists_minimal_subshifts_commutator_fullGroup_not_isomorphic
-- name    : JuschenkoMonod.exists_minimal_subshifts_commutator_fullGroup_not_isomorphic
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:31:32.26422+00:00
-- url     : https://prove2.me/theorems/d0b4e5b7-2251-4410-a731-f521e55b439e
-- title:
--   Matui, p. 246 — an uncountable family of minimal subshifts, distinguished by entropy, whose commutator subgroups are pairwise non-isomorphic finitely generated simple groups
-- statement:
--   There is a family $(S_r)_{r \in \mathbf R}$ of subshifts over finite alphabets $\{0, \dots, m_r - 1\}$, each a Cantor space on which the shift $\tau$ is minimal, such that:
--   - for each $r$, the commutator subgroup $[[\tau|_{S_r}]]'$ is infinite, finitely generated and simple;
--   - for $r \ne s$, the shifts on $S_r$ and $S_s$ have different topological entropy;
--   - for $r \ne s$, $[[\tau|_{S_r}]]'$ and $[[\tau|_{S_s}]]'$ are not isomorphic.
--
--   Moreover, entropy is an invariant of the group: for any two subshifts $P$, $Q$ over finite alphabets that are Cantor spaces with minimal shifts, if the commutator subgroups $[[\tau|_P]]'$ and $[[\tau|_Q]]'$ are isomorphic, then the shifts on $P$ and $Q$ have the same topological entropy.
--
--   Topological entropy is Mathlib's `Dynamics.coverEntropy` of the whole space, for the uniform structure of the product of discrete alphabets.
--
--   *Formalization note.* "A new uncountable family" is stated as a family indexed by $\mathbf R$, the size that Corollary B's "$2^{\aleph_0}$" uses. "Since subshifts can be distinguished by their entropy" is stated as distinct entropies within the family, together with the entropy of a minimal subshift as an isomorphism invariant of its commutator subgroup. Each group in the family is also stated to be finitely generated and simple, as the sentence asserts, and infinite, as the preceding sentence ("this simple (infinite) group") asserts.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 775, Matui's uncountable family, which cites Matui, H., Some remarks on topological full groups of Cantor minimal systems, Internat. J. Math. 17 (2006) 231–251, https://doi.org/10.1142/S0129167X06003448, p. 246

import Mathlib
import Definitions.Def_CantorSystems
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem exists_minimal_subshifts_commutator_fullGroup_not_isomorphic :
    ∃ (m : ℝ → ℕ) (S : ∀ r, CantorSystems.Subshift ℤ (Fin (m r))),
      (∀ r, CantorSystems.IsCantorSpace (S r) ∧ IsMinimal (shiftHomeomorph (S r)) ∧
        Infinite (commutator (fullGroup (shiftHomeomorph (S r)))) ∧
        Group.FG (commutator (fullGroup (shiftHomeomorph (S r)))) ∧
        IsSimpleGroup (commutator (fullGroup (shiftHomeomorph (S r))))) ∧
      (∀ r s, r ≠ s → subshiftEntropy (S r) ≠ subshiftEntropy (S s)) ∧
      (∀ r s, r ≠ s → IsEmpty (commutator (fullGroup (shiftHomeomorph (S r))) ≃*
        commutator (fullGroup (shiftHomeomorph (S s))))) ∧
      ∀ (k l : ℕ) (P : CantorSystems.Subshift ℤ (Fin k)) (Q : CantorSystems.Subshift ℤ (Fin l)),
        CantorSystems.IsCantorSpace P → CantorSystems.IsCantorSpace Q →
        IsMinimal (shiftHomeomorph P) → IsMinimal (shiftHomeomorph Q) →
        Nonempty (commutator (fullGroup (shiftHomeomorph P)) ≃*
          commutator (fullGroup (shiftHomeomorph Q))) →
        subshiftEntropy P = subshiftEntropy Q := by
  sorry

end JuschenkoMonod
