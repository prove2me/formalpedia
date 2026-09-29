-- Prove2me | Theorems.Thm_LocalSearchFL_KMedian_exists_swaps_four_properties
-- name    : LocalSearchFL.KMedian.exists_swaps_four_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:12:03.982486+00:00
-- url     : https://prove2.me/theorems/b5499683-d5f4-4123-a2ed-273748faadc4
-- title:
--   The $k$ swaps of §3.2 and their four properties
-- statement:
--   Let $S$ and $O$ be finite sets of facilities with $|S| = |O|$, and let $\sigma_S, \sigma_O : C \to F$ be assignments of the clients, with capture, good and bad facilities as in Definition 3.1. Then there is a choice, for every $o \in O$, of a facility $\eta(o) \in S$ — the swap $\langle \eta(o), o\rangle$ — such that
--
--   1. each $o \in O$ is considered in exactly one swap;
--   2. a facility $s \in S$ which captures more than one facility in $O$ is not considered in any swap;
--   3. each good facility $s \in S$ is considered in at most two swaps: $|\{o \in O : \eta(o) = s\}| \le 2$;
--   4. if the swap $\langle s, o\rangle$ is considered, then $s$ captures no facility $o' \in O$ with $o' \ne o$.
--
--   These are the swaps whose inequalities (2) are added up in the proof of Theorem 3.2.
--
--   **Formalization Note** Property 1 is built into $\eta$ being a function on $O$. The hypothesis $|S| = |O|$ is the case the paper treats ("we now consider $k$ swaps, one for each facility in $O$"). The assignments are arbitrary maps; the paper's are nearest-facility assignments.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, pp. 549–550, §3.2, the k swaps and their properties 1–4

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures

namespace LocalSearchFL.KMedian

/-- The k swaps of §3.2 (pp. 549–550): when `|S| = |O|`, one can assign to each `o ∈ O` a
facility `η o ∈ S` (the swap `⟨η o, o⟩`) such that
(1) each `o ∈ O` is in exactly one swap (built into `η` being a function on `O`);
(2) a facility of `S` capturing more than one facility of `O` is in no swap;
(3) each good facility of `S` is in at most two swaps;
(4) if `⟨s, o⟩` is a swap, then `s` captures no facility `o' ∈ O` with `o' ≠ o`. -/
theorem exists_swaps_four_properties {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) :
    ∃ η : Fa → Fa,
      (∀ o ∈ O, η o ∈ S) ∧
      (∀ s ∈ S, (∃ o₁ ∈ O, ∃ o₂ ∈ O, o₁ ≠ o₂ ∧ captures σS σO s o₁ ∧ captures σS σO s o₂) →
        ∀ o ∈ O, η o ≠ s) ∧
      (∀ s ∈ S, IsGood σS σO O s → (O.filter (fun o => η o = s)).card ≤ 2) ∧
      (∀ o ∈ O, ∀ o' ∈ O, o' ≠ o → ¬ captures σS σO (η o) o') := by sorry

end LocalSearchFL.KMedian
