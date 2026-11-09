-- Prove2me | Theorems.Thm_IntADSat_lemma_B_6
-- name    : IntADSat.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:54:00.339082+00:00
-- url     : https://prove2.me/theorems/e4f5f427-b63c-4fc3-867c-695fb2540a46
-- title:
--   Lemma B.6 — separated extreme degrees
-- statement:
--   Let $G\sim G(n,1/2)$ and let $k,r,g$ be the parameters of (B.1). With failure probability at most $n^{-0.15+o(1)}$, the $r+1$ largest degrees are pairwise separated by more than $g$. Let $S$ consist of the $r$ vertices of largest degree on this event. Then each vertex of $S$ is a singleton degree class. Moreover, if $C\cap S=\emptyset$ and $|C|\le k$, the $r$ vertices of largest degree in $G[[n]\setminus C]$ are exactly $S$.
--
--   In the formal statement the second and third sentences are deterministic consequences of the separation event, for all sufficiently large $n$: for every graph and every listing $\sigma(0),\dots,\sigma(r)$ witnessing the separation, with $S=\{\sigma(0),\dots,\sigma(r-1)\}$, (a) no other vertex shares the degree of a vertex of $S$, and (b) for every $C$ disjoint from $S$ with $|C|\le k$, every vertex of $S$ has strictly larger degree in $G[[n]\setminus C]$ than every vertex outside $S\cup C$, and $S_C=S$, where $S_C$ is the set of the $r$ highest-degree vertices of $G[[n]\setminus C]$ (ties broken by label).
--
--   These $r$ vertices supply the initial coordinates of the integer construction, and they stay identifiable after deleting a small row set.
--
--   Differences from the source:
--   - reading: probability at most n^(−0.15+o(1)) → for every δ > 0, eventually probability ≤ n^(−0.15+δ); reason: equivalent to the existence of ε(n) → 0 with bound n^(−0.15+ε(n)); the standard meaning of o(1) in an exponent of an upper bound
--   - reading: the r + 1 largest degrees are pairwise separated by more than g → TopSep: a listing σ of r + 1 distinct vertices with deg σ(j) + g < deg σ(i) for i < j and all other degrees ≤ deg σ(r); reason: equivalent to d_(i) − d_(i+1) > g for 1 ≤ i ≤ r in the sorted degree sequence
--   - reading: consequences "on this event", under (B.1)'s "for sufficiently large n" → eventually in n, for every graph and every witness listing σ; reason: the consequences are deterministic given the event
--   - encoding: the r vertices of largest degree in G[[n] ∖ C] are exactly S → strict domination of every vertex outside S ∪ C, and topSet G C r = S; reason: with |S| = r these say the same
--   - encoding: parameters k, K, s, r, g, t of (B.1) → kP, KP, sP, rP, gP (Nat.floor/Nat.ceil of real powers) and tP (Int.floor, natural log); reason: same values
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.6, p.17 (PDF 18)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_TopSep
import Definitions.Def_IntADSat_topSet
import Definitions.Def_IntADSat_kP
import Definitions.Def_IntADSat_IsTopSepListing
import Definitions.Def_IntADSat_deg
import Definitions.Def_IntADSat_degOut
import Definitions.Def_IntADSat_rP

set_option autoImplicit false

namespace IntADSat

/-- **Lemma B.6** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.17 (PDF 18)). With failure probability at most `n^{−0.15+o(1)}`, the
`r + 1` largest degrees are pairwise separated by more than `g`. Let `S` consist of the `r` vertices of
largest degree on this event. Then each vertex of `S` is a singleton degree class. Moreover, if
`C ∩ S = ∅` and `|C| ≤ k`, the `r` vertices of largest degree in `G[[n] ∖ C]` are exactly `S`.

**Formalization Note** `n^{−0.15+o(1)}` is read as: for every `δ > 0`, eventually at most
`n^{−0.15+δ}`. The deterministic part holds for all large `n` (the paper's "for sufficiently large
`n`" of (B.1)) and every graph and witness listing `σ`; `S` is the image of the first `r` listed
vertices. "The `r` vertices of largest degree in `G[[n] ∖ C]` are exactly `S`" is stated both as strict
domination of every vertex outside `S ∪ C` and as `S_C = S` (`topSet`, labels breaking ties). -/
theorem lemma_B_6 :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
      LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => ¬ TopSep G) ≤ (n : ℝ) ^ (-(0.15 : ℝ) + δ)) ∧
    (∀ᶠ n : ℕ in Filter.atTop, ∀ (G : SimpleGraph (Fin n)) (σ : Fin (rP n + 1) ↪ Fin n),
      IsTopSepListing G σ →
        (∀ i : Fin (rP n + 1), i.val < rP n → ∀ u, u ≠ σ i → deg G u ≠ deg G (σ i)) ∧
        ∀ C : Finset (Fin n),
          (∀ i : Fin (rP n + 1), i.val < rP n → σ i ∉ C) → C.card ≤ kP n →
          (∀ i : Fin (rP n + 1), i.val < rP n → ∀ u, u ∉ C → (∀ j : Fin (rP n + 1), j.val < rP n → u ≠ σ j) →
              degOut G C u < degOut G C (σ i)) ∧
          topSet G C (rP n) =
            Finset.univ.filter fun v => ∃ i : Fin (rP n + 1), i.val < rP n ∧ σ i = v) := by sorry

end IntADSat
