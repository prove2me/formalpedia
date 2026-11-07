-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_B_1
-- name    : GuardedSSSP.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:16.612357+00:00
-- url     : https://prove2.me/theorems/c420ab44-3a04-4439-bc66-d0b283e9ad09
-- title:
--   Lemma B.1 — the benchmark $K_{\mathrm{CA}}(G,s)$ is a finite integer attained by a correct program
-- statement:
--   Fix a finite rooted topology $(G,s)$. Among finite deterministic comparison–addition programs that are correct for every nonnegative weighting,
--
--   1. some correct program $A$ satisfies $C_A(w)+P_A(w)\le K_{\mathrm{CA}}(G,s)$ for every $w\in\mathbb R^E_{\ge0}$;
--   2. every correct program $A$ with $C_A(w)+P_A(w)\le c$ for all $w\in\mathbb R^E_{\ge0}$ has $K_{\mathrm{CA}}(G,s)\le c$.
--
--   Together, $K_{\mathrm{CA}}(G,s)=\inf_A\sup_w(C_A(w)+P_A(w))$ is a finite nonnegative integer and the infimum is attained.
--
--   This makes the benchmark of Theorem 1.1 well defined.
--
--   Differences from the source:
--   - reading: finite deterministic comparison–addition programs → finite ternary decision trees with real literals (CAProg); reason: a program with free discrete state and finite worst case unrolls into a tree with the same per-input counts (§4.1)
--   - encoding: the infimum is a finite nonnegative integer and is attained → a correct program with cost ≤ KCA on the orthant, plus the infimum property of KCA; reason: KCA is an sInf over ℕ; attainment is the nonemptiness of that set
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma B.1, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist
import Definitions.Def_GuardedSSSP_KCA

namespace GuardedSSSP

open AtomicDynRouting.ResidenceTime

/-- **Lemma B.1** (Attainment of the numerical benchmark), p.31 (PDF p.32).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "Fix a finite rooted topology. Among finite deterministic
comparison–addition programs correct for every nonnegative primitive weighting, the infimum
K = K_CA(G, s) = inf_A sup_w (C_A(w) + P_A(w)) is a finite nonnegative integer and is attained by one such
program."

For every finite rooted topology `(G, s)`: some correct program has worst-case cost at most `KCA G s` on
the whole nonnegative orthant (attainment, and hence finiteness), and every correct program whose cost is
at most `c` on the orthant has `KCA G s ≤ c` (`KCA G s` is the infimum).

**Formalization Note.** `KCA G s` is a natural number by definition; the content is that the set in its
`sInf` is nonempty. The second clause is the defining property of `sInf`, included so that the item reads
as "the minimum is attained". -/
theorem lemma_B_1 {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) :
    (∃ A : CAProg n, Correct G s A ∧
      ∀ w : Fin m → ℝ, (∀ e, 0 ≤ w e) → A.C w + A.P w ≤ KCA G s) ∧
    (∀ A : CAProg n, Correct G s A → ∀ c : ℕ,
      (∀ w : Fin m → ℝ, (∀ e, 0 ≤ w e) → A.C w + A.P w ≤ c) → KCA G s ≤ c) := by sorry

end GuardedSSSP
