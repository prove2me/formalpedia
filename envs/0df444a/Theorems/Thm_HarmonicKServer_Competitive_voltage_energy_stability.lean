-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_voltage_energy_stability
-- name    : HarmonicKServer.Competitive.voltage_energy_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:44.626955+00:00
-- url     : https://prove2.me/theorems/967fbb4d-67d6-4285-8aed-3b29cf19fdcc
-- title:
--   Lemma 4.3 — Voltage and energy stability
-- statement:
--   Let $k\ge2$, let $Y$ be a distinct-location adversary configuration, and let $a$ be any real zero-sum supply vector. Put $T=\sum_i\max\{a_i,0\}$. Every voltage vector of every minimizing flow satisfies
--   $$|h_i-h_j|\le T\,d(y_i,y_j).$$
--   If label $\ell$ moves to $v$ and the resulting $Y'$ also has distinct locations, then, with $\delta=d(y_\ell,v)$,
--   $$E_{Y'}(a)\le E_Y(a)+2T^2\delta.$$
--   Both conclusions apply to arbitrary real zero-sum supplies, not only the imbalances arising from occupancies. The second bound measures sensitivity to changing the metric-resistance network.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: an adversary move from Y to Y prime with the distinct-location convention → Y prime is Function.update Y i v and both configurations are injective; reason: this specifies one labelled move without restricting its distance, including zero
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 9, Lemma 4.3 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Electrical
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Lemma 4.3, both the voltage and the moved-network energy estimates. -/
theorem voltage_energy_stability {k : ℕ} (hk : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (hY : Function.Injective Y) (a : Vector k) (ha : ZeroSum a) :
    (∀ (F : Flow k) (h : Vector k), Minimizing Y a F → Ohm Y F h →
      ∀ i j, |h i - h j| ≤ supply a * dist (Y i) (Y j)) ∧
    (∀ (i : Fin k) (v : V), Function.Injective (relocate Y i v) →
      energy (relocate Y i v) a ≤ energy Y a + 2 * (supply a)^2 * dist (Y i) v) := by sorry

end HarmonicKServer.Competitive
