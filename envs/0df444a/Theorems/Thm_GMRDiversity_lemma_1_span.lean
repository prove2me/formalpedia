-- Prove2me | Theorems.Thm_GMRDiversity_lemma_1_span
-- name    : GMRDiversity.lemma_1_span
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:41:23.752826+00:00
-- url     : https://prove2.me/theorems/68ca20fb-2b5d-46b0-a807-ec163f97cb75
-- title:
--   Proof of Lemma 1 — recombination does not enlarge the span; $\dim S_j\le\min\{w,j-1\}$
-- statement:
--   Let $\pi$ be a live-pool policy with pool size at most $w$, and consider one round: from the pool $P$, after an action $a$ produced the candidate $z$ with feedback bit $r$, the policy moves to a pool $P'$ in the support of its keep kernel. Write $\operatorname{span}(Q)$ for the span of the first coordinates of a pool $Q$. Then:
--
--   1. if $z=P[i]\oplus P[j]$ is a recombination, its first coordinate lies in $\operatorname{span}\{P[i]_1,P[j]_1\}$ and $\operatorname{span}(P')\le\operatorname{span}(P)$;
--   2. in every case $\operatorname{span}(P')\le\operatorname{span}(P)+\operatorname{span}\{z_1\}$, so only generation can introduce a new direction;
--   3. for every $j$ and vectors $A_1,\dots,A_{j-1}$, if $\operatorname{span}(P')\le\operatorname{span}(A_1,\dots,A_{j-1})$ then
--   $$
--   \dim\operatorname{span}(P')\le\min\{w,\,j-1\}.
--   $$
--
--   Applied along a run, with $A_1,A_2,\dots$ the generated vectors, this gives the bound $\dim S_j\le\min\{w,j-1\}$ on the span of the pool just before the $j$-th generation.
--
--   Differences from the source:
--   - generalization: the pool S_j immediately before the j-th generation of a run → one transition P → P' of the keep kernel, and any P' whose span lies in the span of any j − 1 vectors; reason: iterating the one-step statement along a run, with A_1, …, A_{j−1} the generated vectors, gives the page's bound
--   - generalization: every policy with live pool size at most w → every LivePoolPolicy n w, whose next pool may hold any element of the F₂-span of the previous pool and the new candidate; reason: this class contains the page's policies under every reading of 'previously queried candidates', so the bound for it implies the page's
--   - encoding: the general GMR framework of Definition 1 with costs c(Gen_x) = c(XOR) = 1 → only the parity instance: candidates V n × ZMod 2, Gen_x as genLaw, XOR as +, U_x as hit; reason: T counts queries, so costs play no role; the page's statements concern 𝔊^par_x only
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 1, pp.9–10

import Mathlib
import Definitions.Def_GMRDiversity_LivePoolPolicy
import Definitions.Def_GMRDiversity_poolSpan

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 1: recombination does not enlarge the span, and `dim S_j ≤ min{w, j − 1}`**
(Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with Optimization Guided Operators*, STOC 2027
submission, manuscript sha256 f89f4f77…, proof of Lemma 1, pp.9–10). One round of a live-pool policy
moves from the pool `P` to a pool `P'` in the support of `keep t P a z r`. Then:
1. if `z = XOR(P[i], P[j])`, then `z.1 ∈ span{P[i].1, P[j].1}` and the span of the first
   coordinates of the pool does not grow;
2. in any case the span of `P'` lies in the span of `P` and the new vector `z.1` (only generation
   can introduce a new direction);
3. if the first coordinates of `P'` lie in the span of `j − 1` vectors `A₁, …, A_{j−1}`, then the
   span of `P'` has dimension at most `min{w, j − 1}`. -/
theorem lemma_1_span {n w : ℕ} (π : LivePoolPolicy n w) (t : ℕ) (P : List (Cand n))
    (a : Option (Fin P.length × Fin P.length)) (z : Cand n) (r : Bool) (P' : List (Cand n))
    (hP' : P' ∈ (π.keep t P a z r).support) :
    (∀ i j : Fin P.length, z = P.get i + P.get j →
      z.1 ∈ Submodule.span (ZMod 2) {(P.get i).1, (P.get j).1} ∧ poolSpan P' ≤ poolSpan P) ∧
    poolSpan P' ≤ poolSpan P ⊔ Submodule.span (ZMod 2) {z.1} ∧
    (∀ (j : ℕ) (A : Fin (j - 1) → V n), poolSpan P' ≤ Submodule.span (ZMod 2) (Set.range A) →
      Module.finrank (ZMod 2) (poolSpan P') ≤ min w (j - 1)) := by sorry

end GMRDiversity
