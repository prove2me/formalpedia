-- Prove2me | Theorems.Thm_LittleCharity_EFX_lemma_4_b
-- name    : LittleCharity.EFX.lemma_4_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:32.355065+00:00
-- url     : https://prove2.me/theorems/91fa60f3-75ae-4204-aedf-e67d56fcc91b
-- title:
--   Lemma 4(b) — failure of U0 yields a small envied subset
-- statement:
--   Let $X$ be an EFX allocation under monotone valuations, and suppose Rule $U_0$ is not applicable: for no pool good $g$ and no agent $i$ is the allocation obtained by giving $g$ to $i$ EFX. Then for every source $s$ of $G_X$ and every good $g\in P(X)$:
--
--   1. some agent $j\ne s$ envies the enlarged bundle, $v_j(X_s\cup\{g\})>v_j(X_j)$;
--   2. every inclusion-wise minimal envied subset $Z$ of $X_s\cup\{g\}$ satisfies
--   $$
--   |Z|\le|X_s| .
--   $$
--
--   This guarantees that the sets $X_s\cup\{g\}$ used by Rules $U_1$ and $U_2$ are envied and that a minimal envied subset leaves at least one good of it unassigned.
--
--   **Formalization Note** The hypothesis that $X$ is EFX is Algorithm 1's invariant (p. 8), in force wherever the lemma is applied; it is added because without it $U_0$ could fail for reasons unrelated to $g$. Non-applicability of $U_0$ follows Algorithm 2's precondition (any agent $i$), whereas the prose before Lemma 4 speaks of adding the good to a source; the Lean hypothesis is the precondition's version.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 9–10, Lemma 4(b)

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace LittleCharity.EFX

theorem lemma_4_b {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hmono : IsMonotoneVal v) (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (hEFX : IsEFX v X)
    (hU0 : ¬ U0Applicable v X) :
    ∀ s, IsSource v X s → ∀ g ∈ pool X,
      (∃ j, j ≠ s ∧ v j (X j) < v j (insert g (X s))) ∧
      (∀ Z, IsMinimalEnviedSubset v X (insert g (X s)) Z →
        Z.card ≤ (X s).card) := by sorry
end LittleCharity.EFX
