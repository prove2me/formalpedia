-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_harmonic_protocol
-- name    : HarmonicKServer.Competitive.harmonic_protocol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:57.990642+00:00
-- url     : https://prove2.me/theorems/40509040-650b-4d38-8b3a-446a38524d69
-- title:
--   §2 — Probability normalization and finite-history law
-- statement:
--   For $k\ge1$, every metric configuration $X$, request $r$ and actual Harmonic transition have nonnegative label probabilities summing to one:
--   $$\sum_i p_i(X,r)=1.$$
--   Each outcome covers $r$. A covered request leaves $X$ fixed and costs zero. An uncovered request has $Z_r>0$ and moving label $i$ costs exactly $d(x_i,r)$. For every causal policy and every finite horizon, the finite history weights also sum to one:
--   $$\sum_{w\in[k]^N}P_A(w)=1.$$
--   These are the operational probability obligations implicit in the algorithm definition in Section 2. They include collocated online servers, with repeated labels counted separately, and $N=0$.
--
--   Differences from the source:
--   - encoding: randomized serving rule on [k] → finite nonnegative label law, deterministic dummy label zero on covered requests, and product history weights; reason: the dummy label changes no configuration or cost and introduces no observable random choice; the history law is the iterated specified kernel
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, §2 definition of Harmonic and its conditional label probabilities (unnumbered) (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Interaction

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Section 2's actual probability kernel and its finite-history law. -/
theorem harmonic_protocol {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (X Y : KServer.Config k V) (r : V) :
    (∀ i, 0 ≤ harmonicProbability X r i) ∧
    (∑ i, harmonicProbability X r i = 1) ∧
    (∀ i, Covers (harmonicNext X r i) r) ∧
    (Covers X r → ∀ i, harmonicNext X r i = X ∧ harmonicCost X r i = 0) ∧
    (¬ Covers X r → 0 < normalizer X r ∧
      ∀ i, harmonicCost X r i = dist (X i) r) ∧
    (∀ (A : Adversary k V) (N : ℕ),
      ∑ w : Fin N → Fin k, pathWeight A X Y (List.ofFn w) = 1) := by sorry

end HarmonicKServer.Competitive
