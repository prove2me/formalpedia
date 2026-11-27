-- Prove2me | Theorems.Thm_LefebvreVariations_condorcet_cycle_five_voters_540_profiles
-- name    : LefebvreVariations.condorcet_cycle_five_voters_540_profiles
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:20:58.22887+00:00
-- url     : https://prove2.me/theorems/6350d70b-8ebb-51e5-b657-85ba7babef63
-- title:
--   Lefebvre's variations, No. 258 — on a theme by Condorcet: exactly 540 of the 7776 five-voter profiles on three candidates have a majority cycle
-- statement:
--   Five voters each rank three candidates strictly. Candidate $a$ beats $b$ if at least three voters rank $a$ above $b$. Exactly $540$ of the $6^5=7776$ profiles contain a majority cycle:
--   $$\#\{p:\ \exists a,b,c,\ a\succ_p b\succ_p c\succ_p a\}=540,\qquad \frac{540}{7776}=\frac5{72}\approx 6.94\%.$$
--
--   For three voters the proportion is $1/18\approx5.56\%$, and as the electorate grows the proportion under the impartial culture tends to the Guilbaud limit of about $8.77\%$; five voters is the next odd size after three.
--
--   **Formalization Note** A profile is \texttt{p : Fin 5 $\to$ Equiv.Perm (Fin 3)}, with \texttt{p v c} the rank of candidate $c$ for voter $v$ (lower is better). The count is the cardinality of the \texttt{Finset.univ.filter} of profiles for which three candidates $a,b,c$ form a cycle of strict majorities (at least $3$ of $5$ voters).
--
--   **Why this is a variation.** No open platform problem on the probability of the Condorcet paradox was found; this is the five-voter case of the classical question of the likelihood of majority cycles under the impartial culture (Guilbaud's limit, finite values by Gehrlein). The count is a finite enumeration over 7776 profiles. No formal link to a platform parent is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Marquis de Condorcet (1785); G. Th. Guilbaud, Economie appliquee 5 (1952) for the limit; W. V. Gehrlein for finite-electorate values (all cited from memory). The count 540 of 7776 was obtained here by direct enumeration in Python.

import Mathlib

namespace LefebvreVariations

/-- Among the `6⁵ = 7776` profiles of five voters with strict rankings of three candidates,
exactly 540 (5/72, about 6.94 %) produce a cycle in the pairwise majority relation. `p v c` is the
rank of candidate `c` for voter `v` (lower = better), and candidate `a` beats `b` when at least
three of the five voters rank `a` above `b`. Source: Condorcet's paradox (1785); the limiting
probability under the impartial culture, about 8.77 %, is due to Guilbaud (1952) and finite
electorates were tabulated by Gehrlein (both cited from memory); the count 540 is a direct
enumeration. -/
theorem condorcet_cycle_five_voters_540_profiles :
    (Finset.univ.filter (fun p : Fin 5 → Equiv.Perm (Fin 3) =>
      ∃ a b c : Fin 3,
        3 ≤ (Finset.univ.filter (fun v : Fin 5 => p v a < p v b)).card ∧
        3 ≤ (Finset.univ.filter (fun v : Fin 5 => p v b < p v c)).card ∧
        3 ≤ (Finset.univ.filter (fun v : Fin 5 => p v c < p v a)).card)).card = 540 := by
  sorry

end LefebvreVariations
