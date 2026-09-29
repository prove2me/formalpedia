-- Prove2me | Theorems.Thm_MasekPaterson_FourRussians_possibleSteps_finite
-- name    : MasekPaterson.FourRussians.possibleSteps_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:06:12.933982+00:00
-- url     : https://prove2.me/theorems/260c9128-2e88-45b3-b290-0cd9b866255f
-- title:
--   Lemma 4 — discrete costs give finitely many possible steps
-- statement:
--   Let $\Sigma$ be a finite alphabet and $\gamma$ a nonnegative cost function whose cost set $\Omega = \{D_a\} \cup \{I_a\} \cup \{R_{a,b}\}$ is discrete, i.e. there is $r > 0$ such that every element of $\Omega$ is an integral multiple of $r$. Then the set of possible steps
--
--   $$\{\delta_{i,j} - \delta_{i-1,j}\} \cup \{\delta_{i,j} - \delta_{i,j-1}\},$$
--
--   taken over all strings $A, B \in \Sigma^*$ and all adjacent pairs of entries of their edit matrices, is finite.
--
--   This is what makes the precomputation of Algorithm Y finite: its table ranges over pairs of length-$m$ strings and pairs of length-$m$ vectors of possible steps, a set whose size does not depend on the strings being compared.
--
--   **Formalization Note** Normalization of $\gamma$ is not assumed. Steps on the boundary row and column of the matrix are included in the set.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 23, Lemma 4

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Shared_steps
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Lemma 4: over a finite alphabet, if the set `Ω` of edit costs is discrete then the set
of possible steps in edit matrices is finite. -/
theorem possibleSteps_finite {α : Type*} [Fintype α] (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hΩ : IsDiscrete γ) :
    (possibleSteps γ).Finite := by sorry

end MasekPaterson.FourRussians
