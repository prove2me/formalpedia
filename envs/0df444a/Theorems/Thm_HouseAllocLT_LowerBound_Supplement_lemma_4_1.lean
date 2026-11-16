-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_1
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:15:23.688059+00:00
-- url     : https://prove2.me/theorems/41f641bb-549b-4940-b377-91b81f8f4d4f
-- title:
--   Lemma 4.1 — RPG maximizes the class vector, keeps accepted classes, is Pareto optimal, and its prefix counts are truncated sizes
-- statement:
--   Let $n,m\ge1$, let $\mathrm{MM}$ be any deterministic maximum-matching routine and $P$ any profile (ties, incomplete and empty lists allowed). For every agent order $\pi$, the RPG output $M_\pi(P)$:
--
--   1. is feasible and has the lexicographically largest class vector $z_\pi$ among all matchings feasible at $P$;
--   2. gives every agent accepted at rank $j$ an object of its class $C_j^i$;
--   3. is Pareto optimal at $P$.
--
--   Moreover, for every rank threshold $h\ge1$,
--   $$X_h^{\mathrm{RPG}}(P)=\mathbb E_\pi\big|M_\pi(P^{\le h})\big|,$$
--   the expected number assigned within ranks $1,\ldots,h$ equals the expected output size when every list ends after rank $h$.
--
--   This lemma underlies the PO clause of Theorem 4.1 and the reduction to truncated lists in Lemma 4.5.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine `MM`; reason: the source states the result for whatever fixed routine RPG uses, which is the same claim
--   - encoding: RPG lottery over the n! orders → count of orders whose output, projected onto feasible matchings, equals μ, divided by n!; reason: every RPG output is feasible, so the projection is the identity and the lottery is the source's
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.1, PDF p. 11 (printed p. 9); proof PDF pp. 15–16 (printed pp. 13–14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_RPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.1, PDF p. 11 (printed p. 9). For every routine, profile and order, RPG returns a
matching with the lexicographically largest class vector `z_π`; every accepted agent keeps its
selected class; every output is Pareto optimal; and the expected prefix count through rank `h`
equals the expected output size when all lists end after rank `h`. -/
theorem lemma_4_1 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (MM : MaxMatchingRoutine n m)
    (P : Profile n m) :
    (∀ π : Equiv.Perm (Fin n),
      IsLexBest P (permPos π) (rpgOut MM P π) ∧
      (∀ (i : Fin n) (j : ℕ), (rpgRun MM P π).acc i = some j →
        ∃ a ∈ (P i).classes j, (i, a) ∈ rpgOut MM P π) ∧
      IsParetoOptimal P (rpgOut MM P π)) ∧
    ∀ h : ℕ, 1 ≤ h → expectedPrefix (rpg MM) P h = expectedSize (rpg MM) (truncateProfile P h) := by sorry

end HouseAllocLT.LowerBound.Supplement
