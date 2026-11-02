-- Prove2me | Theorems.Thm_OpenSearchLivenessAbstract_contested_prob_le_abstract
-- name    : OpenSearchLivenessAbstract.contested_prob_le_abstract
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T18:52:24.036792+00:00
-- url     : https://prove2.me/theorems/3c03e304-c763-43d4-8425-f0a59f5ef73b
-- title:
--   Generalized contested-round bound for arbitrary election-timer delays
-- statement:
--   For $n \geq 1$ candidates with arbitrary integer offsets and delay functions over all $2^{64}$ draws, suppose every delay value has at most $K$ preimages: for every candidate $j$ and every integer $t$, at most $K$ draws give delay $t$. Then the fraction of draws in which no candidate fires at least $\delta \geq 1$ before every other candidate is at most $\binom{n}{2}(2\delta-1)K/2^{64}$. The concrete randomized-timer bound is the case $K = 2\lceil 2^{63}/M_{\min}\rceil$. Independence across candidates is an explicit feature of the counting model (draws are a function $\mathrm{Fin}\, n \to \mathrm{Fin}\, 2^{64}$), not a consequence of the point-mass bound.
-- source:
--   OpenSearch cluster coordination, pinned revision b2a54ba5c0defba3d1d20423e911d4bf920bab19 (org.opensearch.cluster.coordination); liveness/timer gap-closure analysis, new theorems mechanized from the branch's OpenSearchCoordination/OpenSearchPreVote/OpenSearchSafety/OpenSearchProgress missions.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic
import Definitions.Def_OpenSearchLivenessAbstract
open OpenSearchLivenessAbstract

theorem OpenSearchLivenessAbstract.contested_prob_le_abstract (n δ K : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (offset : Fin n → Int) (delay : Fin n → Fin (2 ^ 64) → Int)
    (hpre : ∀ j t, (Finset.univ.filter (fun y => delay j y = t)).card ≤ K) :
    ((Finset.univ.filter (fun x => ¬ Uncontested offset delay δ x)).card : ℚ) / (2 ^ 64) ^ n ≤
      (n.choose 2 : ℚ) * (2 * δ - 1 : ℕ) * K / 2 ^ 64 := by sorry
