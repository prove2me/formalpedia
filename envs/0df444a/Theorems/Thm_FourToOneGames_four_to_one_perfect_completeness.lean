-- Prove2me | Theorems.Thm_FourToOneGames_four_to_one_perfect_completeness
-- name    : FourToOneGames.four_to_one_perfect_completeness
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T23:42:22.592799+00:00
-- url     : https://prove2.me/theorems/efc0488a-a669-4e44-94df-fef5af572375
-- title:
--   Theorem 1.6 — hardness of 4-to-1 games with perfect completeness
-- statement:
--   **The 4-to-1 Games Conjecture for $d = 4$ (Khot, CCC 2002), with perfect completeness.** For all $\varepsilon > 0$ there exists $r \in \mathbb{N}^{+}$ such that $\mathrm{Gap\text{-}4\text{-}to\text{-}1}_r(1,\varepsilon)$ is NP-hard: given a $4$-to-1 game $\Psi$ with alphabets of size at most $r$, it is NP-hard to distinguish $\mathrm{val}(\Psi) = 1$ from $\mathrm{val}(\Psi) \le \varepsilon$.
--
--   Hardness is formalized as a polynomial-time gap-preserving reduction from label cover with projection constraints: for every $\varepsilon > 0$ there is a soundness threshold $s \in (0,1)$ such that for every source alphabet bound $r_0$ there are a target alphabet bound $r$ and a polynomial-time computable map $\Psi \mapsto \Phi_\Psi$ with $\Phi_\Psi$ always a $4$-to-1 game over alphabets of size at most $r$, such that $\mathrm{val}(\Psi) = 1$ implies $\mathrm{val}(\Phi_\Psi) = 1$ (perfect completeness) and $\mathrm{val}(\Psi) \le s$ implies $\mathrm{val}(\Phi_\Psi) \le \varepsilon$. Composed with the NP-hardness of $\mathrm{GapPLC}_{r_0}(1,s)$ — the PCP theorem plus the parallel repetition theorem, Theorem 1.2 of the source, which this mission takes as an external input — this is exactly Theorem 1.6.
--
--   The polynomial-time computability requirement is essential: without it the statement would be satisfied by a map that inspects the value of its input and returns one of two fixed instances.
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, p. 5, Theorem 1.6 (see also Conjecture 1.5, p. 5)

import Definitions.Def_FourToOneGames_LabelCover

namespace FourToOneGames

theorem four_to_one_perfect_completeness :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ r₀ : ℕ, ∃ r : ℕ,
      Nonempty (GapReduction encodeLabelCover encodeLabelCover
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val = 1)
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val ≤ s)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val = 1)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val ≤ ε)) := by
  sorry

end FourToOneGames
