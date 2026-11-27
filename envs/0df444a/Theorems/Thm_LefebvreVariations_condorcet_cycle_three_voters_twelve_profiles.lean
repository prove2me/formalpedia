-- Prove2me | Theorems.Thm_LefebvreVariations_condorcet_cycle_three_voters_twelve_profiles
-- name    : LefebvreVariations.condorcet_cycle_three_voters_twelve_profiles
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:20:42.060254+00:00
-- url     : https://prove2.me/theorems/d423d406-e1a0-5a54-ba2d-3fd843c9d4e3
-- title:
--   Lefebvre's variations, No. 257 — on a theme by Condorcet: exactly 12 of the 216 three-voter profiles on three candidates have a majority cycle
-- statement:
--   Three voters each rank three candidates strictly (a profile is a triple of permutations). Candidate $a$ beats $b$ if at least two voters rank $a$ above $b$. Exactly $12$ of the $6^3=216$ profiles contain a majority cycle $a\succ b\succ c\succ a$:
--   $$\#\{p:\ \exists a,b,c,\ a\succ_p b\succ_p c\succ_p a\}=12,\qquad \frac{12}{216}=\frac1{18}.$$
--
--   This is the Condorcet paradox at its smallest size. The cyclic profiles are those where the three voters hold the three cyclic rotations of one ranking, $abc,\,bca,\,cab$, or of its reverse, in any assignment to the voters. The probability of a cycle under the impartial culture approaches, as the electorate grows, the Guilbaud limit of about $8.77\%$.
--
--   **Formalization Note** A profile is \texttt{p : Fin 3 $\to$ Equiv.Perm (Fin 3)}, with \texttt{p v c} the rank of candidate $c$ for voter $v$ (lower is better). The count is the cardinality of the \texttt{Finset.univ.filter} of profiles for which three candidates $a,b,c$ (not required to be distinct, which makes no difference since a strict relation cannot loop on fewer than three) form a cycle.
--
--   **Why this is a variation.** No open platform problem on the probability of the Condorcet paradox was found; this is the first size of the classical question of the likelihood of majority cycles under the impartial culture (Guilbaud's limit, finite-electorate values by Gehrlein). The count is a finite enumeration. No formal link to a platform parent is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Marquis de Condorcet (1785), the voting paradox; G. Th. Guilbaud, "Les theories de l'interet general et le probleme logique de l'agregation", Economie appliquee 5 (1952), the limiting probability (both cited from memory). The count 12 of 216 was obtained here by direct enumeration in Python.

import Mathlib

namespace LefebvreVariations

/-- Among the `6³ = 216` profiles of three voters with strict rankings of three candidates, exactly
12 (one in 18) produce a cycle in the pairwise majority relation. `p v c` is the rank of candidate
`c` for voter `v` (lower = better), and candidate `a` beats `b` when at least two voters rank `a`
above `b`. Source: Condorcet's paradox (1785); the probability of a cycle under the impartial
culture is due to Guilbaud (1952) in the limit and to Gehrlein for finite electorates (cited from
memory); the count 12 is a direct enumeration. -/
theorem condorcet_cycle_three_voters_twelve_profiles :
    (Finset.univ.filter (fun p : Fin 3 → Equiv.Perm (Fin 3) =>
      ∃ a b c : Fin 3,
        2 ≤ (Finset.univ.filter (fun v : Fin 3 => p v a < p v b)).card ∧
        2 ≤ (Finset.univ.filter (fun v : Fin 3 => p v b < p v c)).card ∧
        2 ≤ (Finset.univ.filter (fun v : Fin 3 => p v c < p v a)).card)).card = 12 := by
  sorry

end LefebvreVariations
