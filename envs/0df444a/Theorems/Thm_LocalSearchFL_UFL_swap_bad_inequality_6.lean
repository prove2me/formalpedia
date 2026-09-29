-- Prove2me | Theorems.Thm_LocalSearchFL_UFL_swap_bad_inequality_6
-- name    : LocalSearchFL.UFL.swap_bad_inequality_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:17:23.229251+00:00
-- url     : https://prove2.me/theorems/c3524761-45ff-45bd-af52-d6df29b38ce9
-- title:
--   Inequality (6) — swapping a bad facility with its nearest captured facility
-- statement:
--   Let $f_i \ge 0$ be facility opening costs on a metric instance, let $S$ be a nonempty set of facilities that is locally optimum for the add/drop/swap neighbourhood (4), and let $O$ be any solution. Let $\sigma_S$, $\sigma_O$ be nearest-facility assignments for $S$ and $O$, write $S_j = c_{j\sigma_S(j)}$ and $O_j = c_{j\sigma_O(j)}$, and let $\pi$ be a permutation of the clients satisfying the three conditions of the mapping of the proof of Lemma 4.2.
--
--   Let $s \in S$ capture $o \in O$, where $o$ is nearest to $s$ among the facilities of $O$ captured by $s$: $c_{so} \le c_{so'}$ for every $o' \in O$ captured by $s$. Then
--   $$\begin{aligned} f_o - f_s &+ \sum_{\substack{j \in N_S(s)\\ \pi(j) \neq j}} \bigl(O_j + O_{\pi(j)} + S_{\pi(j)} - S_j\bigr) \\ &+ \sum_{\substack{j \in N_O(o),\\ \pi(j) = j \in N_S(s)}} (O_j - S_j) + \sum_{\substack{j \notin N_O(o),\\ \pi(j) = j \in N_S(s)}} (S_j + S_j + O_j - S_j) \ \ge\ 0. \end{aligned}$$
--
--   This is the information extracted from the swap $\langle s, o\rangle$ that closes a bad facility $s$ and opens $o$; it is the main ingredient of inequality (8).
--
--   **Formalization Note** The distance $c_{so}$ between two facilities is `I.cf s o`. The summand $S_j + S_j + O_j - S_j$ is kept in the paper's unsimplified form.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, pp. 555–556, eq. (6)

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

namespace LocalSearchFL.UFL

/-- Inequality (6), pp. 555–556: the swap `⟨s, o⟩` for a bad facility. Let `S` be a locally
optimum solution for the neighbourhood (4), `O` any solution, `σS`, `σO` nearest-facility
assignments, `π` the mapping of the proof of Lemma 4.2. Let `s ∈ S` capture `o ∈ O`, where `o`
is a facility nearest to `s` among the facilities of `O` captured by `s`
(`c_{so} ≤ c_{so'}` for every `o' ∈ O` captured by `s`). Then
`f_o − f_s + ∑_{j ∈ N_S(s), π(j) ≠ j} (O_j + O_{π(j)} + S_{π(j)} − S_j)
  + ∑_{j ∈ N_O(o), π(j) = j ∈ N_S(s)} (O_j − S_j)
  + ∑_{j ∉ N_O(o), π(j) = j ∈ N_S(s)} (S_j + S_j + O_j − S_j) ≥ 0`. -/
theorem swap_bad_inequality_6 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S O : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπ : IsRefinedPi σS σO π)
    (s o : Fa) (hs : s ∈ S) (ho : o ∈ O) (hcap : captures σS σO s o)
    (hnearest : ∀ o' ∈ O, captures σS σO s o' → I.cf s o ≤ I.cf s o') :
    0 ≤ f o - f s +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j),
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j = j ∧ σO j = o),
        (I.c j (σO j) - I.c j (σS j)) +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j = j ∧ σO j ≠ o),
        (I.c j (σS j) + I.c j (σS j) + I.c j (σO j) - I.c j (σS j)) := by sorry

end LocalSearchFL.UFL
