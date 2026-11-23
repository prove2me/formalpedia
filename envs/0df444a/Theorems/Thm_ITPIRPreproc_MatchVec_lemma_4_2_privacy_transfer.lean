-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_lemma_4_2_privacy_transfer
-- name    : ITPIRPreproc.MatchVec.lemma_4_2_privacy_transfer
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:46:03.050927+00:00
-- url     : https://prove2.me/theorems/8b406fa7-a6ba-4857-a8e8-41f20bd1fa97
-- title:
--   Adaptive privacy from the per-index uniform-query invariant
-- statement:
--   Let $S$ satisfy `IndexUniformStep`. Then it satisfies the one-step adaptive-privacy predicate `StepPrivate`.
--
--   Fix a database, a measurable adversary, a round $j$, an adversary-coin event $B$, a query prefix $qs$, and a possible next query $q$. First sum the per-index identity over $i\in[n]$. The measurability clauses make these finitely many indexed-prefix pieces a legitimate disjoint decomposition, yielding
--   $$
--   \Pr[B,\ H_j=qs,\ Q_j=q]
--    =\Pr[B,\ H_j=qs]\,\operatorname{step}_j(qs,q).
--   $$
--   Induction on $j$ and the length of the query history then gives
--   $$\Pr[B,\ H_j=qs]=\Pr[B]\,\Pr[H_j=qs],$$
--   where $\Pr[B]=\operatorname{coinTape}(B)$. Indeed, the empty history is deterministic; the inductive step uses the displayed factorization for the last query, with $B=\Omega$ to identify the new marginal history probability. Combining the two equations is exactly `StepPrivate`.
--
--   This lemma isolates the adaptive-adversary part of the privacy argument; it does not assume perfect privacy or correctness of $S$.
-- source:
--   Dujmovic--Lai--Wichs, STOC 2027 submission #572, §4.2 privacy argument, printed p.15 (PDF p.17): conditional on each prefix, each query is uniform independently of the target; this invariant also holds across epoch boundaries. The finite-index summation and history induction are the formal measure-theoretic rendering of that argument.

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_CompilerRoundModels

open MeasureTheory
open scoped ENNReal

open ITPIRPreproc.MatchVec

theorem ITPIRPreproc.MatchVec.lemma_4_2_privacy_transfer (S : Scheme) (n lam : ℕ)
    (h : IndexUniformStep S n lam) : StepPrivate S n lam := by sorry
