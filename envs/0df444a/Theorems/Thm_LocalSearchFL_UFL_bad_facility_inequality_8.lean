-- Prove2me | Theorems.Thm_LocalSearchFL_UFL_bad_facility_inequality_8
-- name    : LocalSearchFL.UFL.bad_facility_inequality_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:17:49.590989+00:00
-- url     : https://prove2.me/theorems/0a30f0f6-1e3d-400f-8ede-f4359cb48116
-- title:
--   Inequality (8) — the facility cost of a bad facility
-- statement:
--   Let $f_i \ge 0$ be facility opening costs on a metric instance, let $S$ be a nonempty set of facilities that is locally optimum for the add/drop/swap neighbourhood (4), and let $O$ be any solution. Let $\sigma_S$, $\sigma_O$ be nearest-facility assignments for $S$ and $O$, write $S_j = c_{j\sigma_S(j)}$ and $O_j = c_{j\sigma_O(j)}$, and let $\pi$ be a permutation of the clients satisfying the three conditions of the mapping of the proof of Lemma 4.2.
--
--   If $s \in S$ is **bad**, and $P \subseteq O$ is the set of facilities of $O$ that $s$ captures, then
--   $$\sum_{o' \in P} f_{o'} - f_s + \sum_{\substack{j \in N_S(s)\\ \pi(j) \neq j}} \bigl(O_j + O_{\pi(j)} + S_{\pi(j)} - S_j\bigr) + 2 \sum_{\substack{j \in N_S(s)\\ \pi(j) = j}} O_j \ \ge\ 0.$$
--
--   It is the counterpart for bad facilities of inequality (5): adding (5) over the good facilities, (8) over the bad ones, and $f_o \ge 0$ over the facilities of $O$ captured by no one yields Lemma 4.2.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 556, eq. (8) (from eq. (6) and eq. (7))

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

namespace LocalSearchFL.UFL

/-- Inequality (8), p. 556. Let `S` be a locally optimum solution for the neighbourhood (4), `O`
any solution, `σS`, `σO` nearest-facility assignments, `π` the mapping of the proof of
Lemma 4.2. If `s ∈ S` is bad and `P ⊆ O` is the set of facilities that `s` captures, then
`∑_{o' ∈ P} f_{o'} − f_s + ∑_{j ∈ N_S(s), π(j) ≠ j} (O_j + O_{π(j)} + S_{π(j)} − S_j)
  + 2 ∑_{j ∈ N_S(s), π(j) = j} O_j ≥ 0`. -/
theorem bad_facility_inequality_8 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S O : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπ : IsRefinedPi σS σO π)
    (s : Fa) (hs : s ∈ S) (hbad : ¬ IsGood σS σO O s) :
    0 ≤ ∑ o' ∈ O.filter (fun o' => captures σS σO s o'), f o' - f s +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j),
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) +
      2 * ∑ j ∈ (nbhd σS s).filter (fun j => π j = j), I.c j (σO j) := by sorry

end LocalSearchFL.UFL
