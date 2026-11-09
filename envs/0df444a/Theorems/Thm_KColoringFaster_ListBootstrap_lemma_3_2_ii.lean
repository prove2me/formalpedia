-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_lemma_3_2_ii
-- name    : KColoringFaster.ListBootstrap.lemma_3_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:10.90707+00:00
-- url     : https://prove2.me/theorems/72d59f39-4d5f-444f-a668-95921c05160b
-- title:
--   Lemma 3.2 (ii) — singleton propagation
-- statement:
--   Let $(G,L)$ be a list-coloring instance on $\{0,\dots,n-1\}$. Repeatedly fix a singleton list $L(v)=\{c\}$, delete $v$, and delete $c$ from the lists of the remaining neighbours of $v$; stop when a list becomes empty. For every order in which the steps are taken:
--
--   1. after $m$ steps exactly $n-m$ vertices remain, so the process ends after at most $n$ steps, and some sequence of steps reaches a final state (an empty list, or no singleton list);
--   2. no list is ever enlarged;
--   3. if an empty list is produced, $(G,L)$ has no list coloring;
--   4. if a final state has no empty list, then it has no singleton list and its residual instance is equivalent to $(G,L)$: every list coloring of $(G,L)$ restricts to a coloring of the residual instance, the residual instance is colorable if and only if $(G,L)$ is, and every coloring of the residual instance extends uniquely to a list coloring of $G$;
--   5. the outcome of such a sequence of steps (the certificate of infeasibility, or the residual instance) is computed by a deterministic algorithm in time polynomial in the input size.
--
--   The warm-up of §4 runs this propagation after every step; the general algorithm of §5 does not.
--
--   **Formalization Note** Residual instances are represented as the set of remaining vertices with their current lists (see `Normalization`); the algorithm of item 5 is as in `Algorithms`.
--
--   Differences from the source:
--   - generalization: "repeatedly fixing a singleton" (one unspecified order) → every order of the steps; reason: the claims hold for each order, so the source's process is included
--   - reading: "an equivalent residual instance" → restriction of colorings, equal colorability and unique extension; reason: these are the claims of the lemma and its proof (p. 9)
--   - encoding: "produces in polynomial time" → one deterministic program whose cost is at most a polynomial in the input bit size and whose output encodes the final state of some sequence of steps; reason: the integer RAM of `Algorithms`
--   - generalization: nonempty lists → lists may be empty; reason: an empty input list is a final state certifying infeasibility, and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 8, Lemma 3.2 (ii) and its last sentence

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms
import Definitions.Def_KColoringFaster_ListBootstrap_Normalization

open Classical

namespace KColoringFaster.ListBootstrap

/-- Lemma 3.2 (Normalization), part (ii), p. 8. Repeatedly fix a singleton list `L(v) = {c}`, delete
`v` and delete `c` from the lists of its remaining neighbours, stopping when a list is empty. For every
list instance `(G, L)` on `Fin n` and every order of the steps:
1. every run of `m` steps leaves `n - m` vertices, so the process ends after at most `n` steps, and
   some run reaches a final state (an empty list, or no singleton list);
2. lists are never enlarged;
3. a final state with an empty list certifies that `(G, L)` has no list coloring;
4. a final state with no empty list has no singleton list, and its residual instance is equivalent:
   every list coloring of `(G, L)` restricts to a list coloring of the residual instance, the residual
   instance is colorable iff `(G, L)` is, and every list coloring of the residual instance extends
   uniquely to a list coloring of `(G, L)`;
5. a deterministic program computes, in time polynomial in the input bit size, the outcome of some
   such run: `[0]` for an empty list, or the residual instance. -/
theorem lemma_3_2_ii :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (L : Fin n → Finset ℕ) (m : ℕ) (t : PropState n),
      PropReach G (PropState.init L) m t → m + t.S.card = n) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (L : Fin n → Finset ℕ),
      ∃ m t, PropReach G (PropState.init L) m t ∧ t.IsTerminal) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (L : Fin n → Finset ℕ) (m : ℕ) (t : PropState n),
      PropReach G (PropState.init L) m t → ∀ v, t.L v ⊆ L v) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (L : Fin n → Finset ℕ) (m : ℕ) (t : PropState n),
      PropReach G (PropState.init L) m t → t.HasEmpty → ¬ ∃ c, IsListColoringOf G L c) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (L : Fin n → Finset ℕ) (m : ℕ) (t : PropState n),
      PropReach G (PropState.init L) m t → t.IsTerminal → ¬ t.HasEmpty →
        ¬ t.HasSingleton ∧
        (∀ c, IsListColoringOf G L c → IsResidualColoringOf G t c) ∧
        ((∃ φ, IsResidualColoringOf G t φ) ↔ ∃ c, IsListColoringOf G L c) ∧
        ∀ φ, IsResidualColoringOf G t φ →
          ∃! c : Fin n → ℕ, IsListColoringOf G L c ∧ ∀ v ∈ t.S, c v = φ v) ∧
    DetPolyComputes encList (fun _ => True) (fun I out =>
      ∃ m t, PropReach I.G (PropState.init I.L) m t ∧ t.IsTerminal ∧ out = encOutcome t) := by sorry

end KColoringFaster.ListBootstrap
