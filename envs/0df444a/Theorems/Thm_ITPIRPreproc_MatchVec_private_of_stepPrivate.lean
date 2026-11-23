-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_private_of_stepPrivate
-- name    : ITPIRPreproc.MatchVec.private_of_stepPrivate
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:49:59.795107+00:00
-- url     : https://prove2.me/theorems/e27e7085-9ffc-485b-80d7-4d24d0907d45
-- title:
--   One-step query factorization gives perfect adaptive privacy
-- statement:
--   Let $S$ be a preprocessing PIR scheme in the model of §3. Suppose that for every database $D$ there are simulator step probabilities $\sigma_j(q_1,\ldots,q_j;q)$ such that, for every adaptive measurable adversary, every $j$, every measurable event $B$ of the adversary's coins and all query strings,
--   $$
--   \Pr[B\cap\{(Q_1,\ldots,Q_j)=qs\}\cap\{Q_{j+1}=q\}]
--    =\Pr[B]\,\Pr[(Q_1,\ldots,Q_j)=qs]\,\sigma_j(qs,q).
--   $$
--   Then $S$ is perfectly private: the joint law of the adversary's coins and any finite query history is the product of the adversary's independent coin law and a simulator law depending only on the database, database length and security parameter, never on the chosen indices.
--
--   This is the generic induction implicit in the privacy proof of Lemma 4.2. Its unnormalized one-step formulation remains valid on zero-probability prefixes.
--
--   **Formalization Note** The simulator law on $T$ queries is obtained by multiplying the first $T$ one-step factors; the base case is the point mass on the empty query list.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Lemma 4.2 privacy proof, printed pp.14–15 (PDF pp.16–17); perfect-privacy definition in §3, printed p.10 (PDF p.12).

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_CompilerInvariants

open MeasureTheory
open scoped ENNReal

namespace ITPIRPreproc.MatchVec

/-- If each next query has an adversary-independent conditional law, with the joint probability
of every adversary-coin event and query prefix factoring as in `StepPrivate`, then the scheme is
perfectly private in the adaptive experiment of §3. -/
theorem private_of_stepPrivate (S : Scheme) (n lam : ℕ) (h : StepPrivate S n lam) :
    PerfectlyPrivate S n lam := by sorry
