-- Prove2me | Theorems.Thm_LocalSearchFL_UFL_drop_good_inequality_5
-- name    : LocalSearchFL.UFL.drop_good_inequality_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:16:42.053778+00:00
-- url     : https://prove2.me/theorems/7bac64c2-dfd2-4b95-a1a2-4d68c8ff5a52
-- title:
--   Inequality (5) — dropping a good facility
-- statement:
--   Let $f_i \ge 0$ be facility opening costs on a metric instance with at least one client, let $S$ be a nonempty set of facilities that is locally optimum for the add/drop/swap neighbourhood (4), and let $O$ be any solution. Let $\sigma_S$, $\sigma_O$ be nearest-facility assignments for $S$ and $O$, write $S_j = c_{j\sigma_S(j)}$ and $O_j = c_{j\sigma_O(j)}$, and let $\pi$ be a permutation of the clients satisfying the three conditions of the mapping of the proof of Lemma 4.2 (it preserves every $N_O(o)$, satisfies Property 3.1, and fixes the clients of a captured block that it maps into that block).
--
--   If $s \in S$ is **good**, i.e. captures no facility of $O$, then
--   $$-f_s + \sum_{\substack{j \in N_S(s)\\ \pi(j) \neq j}} \bigl(O_j + O_{\pi(j)} + S_{\pi(j)} - S_j\bigr) + 2 \sum_{\substack{j \in N_S(s)\\ \pi(j) = j}} O_j \ \ge\ 0.$$
--
--   The inequality records what the local optimum learns from the drop move that closes a good facility. Summed with inequality (8) for the bad facilities, it gives the facility cost bound of Lemma 4.2.
--
--   **Formalization Note** The instance is required to have at least one client. Then a good facility is never the only open facility, so dropping it is a legal move. With no clients and $S = \{s\}$ the inequality would read $-f_s \ge 0$, which fails; the paper implicitly assumes clients exist.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 555, eq. (5)

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

namespace LocalSearchFL.UFL

/-- Inequality (5), p. 555. Let `S` be a locally optimum solution for the neighbourhood (4), `O`
any solution, `σS`, `σO` nearest-facility assignments for `S` and `O` (so `S_j = c_{j σS(j)}`,
`O_j = c_{j σO(j)}`), and `π` the mapping of the proof of Lemma 4.2. If there is at least one
client and `s ∈ S` is good (captures no `o ∈ O`), then
`−f_s + ∑_{j ∈ N_S(s), π(j) ≠ j} (O_j + O_{π(j)} + S_{π(j)} − S_j)
  + 2 ∑_{j ∈ N_S(s), π(j) = j} O_j ≥ 0`. -/
theorem drop_good_inequality_5 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [Nonempty Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S O : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπ : IsRefinedPi σS σO π)
    (s : Fa) (hs : s ∈ S) (hgood : IsGood σS σO O s) :
    0 ≤ -f s +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j),
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) +
      2 * ∑ j ∈ (nbhd σS s).filter (fun j => π j = j), I.c j (σO j) := by sorry

end LocalSearchFL.UFL
