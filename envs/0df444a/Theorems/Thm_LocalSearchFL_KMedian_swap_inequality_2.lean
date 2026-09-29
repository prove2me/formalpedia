-- Prove2me | Theorems.Thm_LocalSearchFL_KMedian_swap_inequality_2
-- name    : LocalSearchFL.KMedian.swap_inequality_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:12:28.451631+00:00
-- url     : https://prove2.me/theorems/5b6f6c5d-0bd9-4e73-b9ff-fc77d85f4f75
-- title:
--   Inequality (2): the cost bound for a considered swap $\langle s, o\rangle$
-- statement:
--   Consider a metric instance with clients $C$ and facilities $F$. Let $S$ be a nonempty set of facilities that is locally optimum for single swaps, and let $O$ be a set of facilities. Let $\sigma_S$ and $\sigma_O$ be nearest-facility assignments for $S$ and $O$, with service costs $S_j = c_{j\sigma_S(j)}$ and $O_j = c_{j\sigma_O(j)}$ and neighbourhoods $N_S(s)$, $N_O(o)$. Let $\pi : C \to C$ be a bijection that maps every $N_O(o)$ onto itself and satisfies Property 3.1 on every $N_O(o)$: whenever $s$ does not capture $o$, $\pi(N^o_s) \cap N^o_s = \emptyset$.
--
--   If $s \in S$ and $o \in O$ are such that $s$ captures no facility $o' \in O$ with $o' \ne o$, then
--   $$\sum_{j \in N_O(o)} (O_j - S_j) + \sum_{\substack{j \in N_S(s)\\ j \notin N_O(o)}} \bigl(O_j + O_{\pi(j)} + S_{\pi(j)} - S_j\bigr) \ge 0.$$
--
--   Summed over the $k$ swaps of §3.2, these inequalities give $\mathrm{cost}(O) - \mathrm{cost}(S) + 4\,\mathrm{cost}(O) \ge 0$, i.e. Theorem 3.2.
--
--   **Formalization Note** The facilities $s$ and $o$ may coincide or $o$ may lie in $S$ (the paper notes that its inequalities hold even if $S \cap O \ne \emptyset$). The permutation $\pi$ is one permutation of all clients, the union of the bijections of the individual sets $N_O(o)$.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, pp. 550–551, §3.2, eq. (2) (with inequality (1), p. 548)

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures

namespace LocalSearchFL.KMedian

/-- Inequality (2) (pp. 550–551). Let `S` be a locally optimum solution for single swaps, `O`
any solution, `σS`, `σO` nearest-facility assignments for `S` and `O` (so `S_j = c_{j σS(j)}`,
`O_j = c_{j σO(j)}`), and `π` a permutation of the clients that maps each `N_O(o)` onto itself
and satisfies Property 3.1 on each. If `s ∈ S`, `o ∈ O` and `s` captures no `o' ∈ O` other than
`o`, then
`∑_{j ∈ N_O(o)} (O_j − S_j) + ∑_{j ∈ N_S(s), j ∉ N_O(o)} (O_j + O_{π(j)} + S_{π(j)} − S_j) ≥ 0`. -/
theorem swap_inequality_2 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (S O : Finset Fa) (hS : S.Nonempty)
    (hloc : IsSwapLocalOpt I S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπO : ∀ j, σO (π j) = σO j)
    (hπ : ∀ s o : Fa, ¬ captures σS σO s o →
      ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∉ nbhd σO o ∩ nbhd σS s)
    (s o : Fa) (hs : s ∈ S) (ho : o ∈ O)
    (hcap : ∀ o' ∈ O, o' ≠ o → ¬ captures σS σO s o') :
    0 ≤ ∑ j ∈ nbhd σO o, (I.c j (σO j) - I.c j (σS j)) +
      ∑ j ∈ nbhd σS s \ nbhd σO o,
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) := by sorry

end LocalSearchFL.KMedian
