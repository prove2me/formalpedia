-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_private_edge_extension
-- name    : HarmonicKServer.Competitive.private_edge_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:19.856135+00:00
-- url     : https://prove2.me/theorems/2942ff64-64b5-4066-935d-af6c883b804d
-- title:
--   §2 footnote 2 — Distinct private starts and fixed lifting cost
-- statement:
--   Let $k\ge1$, let $X_0,Y_0$ be arbitrary labelled configurations, and let $\varepsilon>0$. There is a metric on $V\sqcup[k]$ with exactly the private-edge distance formula. Its private endpoints are distinct, including when original adversary positions coincide. On old points every Harmonic probability and movement cost is unchanged.
--
--   Every valid adaptive service policy $A$ on $V$ has a valid causal lift $L$ starting the online servers at the old $X_0$ and the adversary servers at the private endpoints. For every completed label history, the next request is the old request embedded into the extension, online accumulated costs are equal, and
--   $$C_L(h)\le C_A(h)+k\varepsilon.$$
--   The same extension and lift work at every horizon. This retains the source reduction for metrics with fewer than $k$ points and leaves the original collocated starts admissible in the headline result.
--
--   Differences from the source:
--   - encoding: attach one private edge per initially labelled adversary server → the disjoint union V plus Fin k with the explicit privateDistance formula; reason: this is the induced path metric on the old space and the private endpoints; no restriction on the original metric or starting tuples is imposed
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, §2 footnote 2 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Interaction
import Definitions.Def_HarmonicKServer_Competitive_Reductions

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Section 2, footnote 2; collocated starts and metrics with fewer than k points are allowed. -/
theorem private_edge_extension {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (X Y : KServer.Config k V) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : MetricSpace (V ⊕ Fin k),
      (∀ u v, @dist (V ⊕ Fin k) m.toDist u v = privateDistance Y ε u v) ∧
      (letI := m
       (Function.Injective (fun i : Fin k => (Sum.inr i : V ⊕ Fin k))) ∧
       (∀ (x : KServer.Config k V) (r : V) (i : Fin k),
         harmonicProbability ((Sum.inl : V → V ⊕ Fin k) ∘ x) (Sum.inl r) i = harmonicProbability x r i ∧
         harmonicCost ((Sum.inl : V → V ⊕ Fin k) ∘ x) (Sum.inl r) i = harmonicCost x r i) ∧
       (∀ A : Adversary k V, ValidAdversary A X Y →
         ∃ L : Adversary k (V ⊕ Fin k),
           ValidAdversary L (Sum.inl ∘ X) Sum.inr ∧
           (∀ h, (L h).request = Sum.inl (A h).request) ∧
           ∀ h : History k,
             (stateAt L (Sum.inl ∘ X) Sum.inr h).onlineCost = (stateAt A X Y h).onlineCost ∧
             (stateAt L (Sum.inl ∘ X) Sum.inr h).adversaryCost ≤
               (stateAt A X Y h).adversaryCost + (k : ℝ) * ε)) := by sorry

end HarmonicKServer.Competitive
