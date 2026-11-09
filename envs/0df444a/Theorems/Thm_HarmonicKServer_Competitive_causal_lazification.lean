-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_causal_lazification
-- name    : HarmonicKServer.Competitive.causal_lazification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:20.158206+00:00
-- url     : https://prove2.me/theorems/44b0bc83-fccf-4efc-9849-f34ef3636f8d
-- title:
--   §2 — Causal lazification with prefix cost domination
-- statement:
--   For $k\ge1$ and arbitrary initial online and adversary configurations, every valid deterministic adaptive service policy $A$ has a valid lazy causal policy $L$. At every completed online label history $h$, both policies issue the same next request, have the same online configuration and accumulated online cost, and
--   $$C_L(h)\le C_A(h).$$
--   The lazy policy moves one server directly to an uncovered request and otherwise stays put. The single history-tree policy $L$ works for all prefixes and horizons, so this is causal lazification rather than a separate offline optimization for each realized request list. It is the source's Section 2 reduction, with randomness handled by the separate arbitrary-seed bridge.
--
--   Differences from the source:
--   - encoding: causal lazification does not increase cost → one lazy policy on the entire completed-label tree, with prefixwise cost domination and identical requests; reason: a deterministic policy and fixed initial data reconstruct the complete past from the history, so this expresses causality without restricting adaptive requests
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, §2, Distinct Adversary Locations; cited causal lazification [MMS90, Lemma 1] (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Interaction

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Section 2's causal lazification, with prefixwise cost domination on the whole history tree. -/
theorem causal_lazification {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (X Y : KServer.Config k V) (A : Adversary k V) (hA : ValidAdversary A X Y) :
    ∃ L : Adversary k V, ValidAdversary L X Y ∧ LazyAdversary L X Y ∧
      ∀ h : History k,
        (L h).request = (A h).request ∧
        (stateAt L X Y h).online = (stateAt A X Y h).online ∧
        (stateAt L X Y h).onlineCost = (stateAt A X Y h).onlineCost ∧
        (stateAt L X Y h).adversaryCost ≤ (stateAt A X Y h).adversaryCost := by sorry

end HarmonicKServer.Competitive
