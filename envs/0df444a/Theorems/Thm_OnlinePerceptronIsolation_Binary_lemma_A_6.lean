-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_lemma_A_6
-- name    : OnlinePerceptronIsolation.Binary.lemma_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:00.106275+00:00
-- url     : https://prove2.me/theorems/60ee4418-cbd4-429b-8a00-4cd65c305ef5
-- title:
--   Lemma A.6 — reduction to deterministic algorithms
-- statement:
--   Fix $m,n$, a real margin $\kappa$, a real isolation radius $h$, and the independent standard Gaussian input law. Let $b_n\in\mathbb R$ satisfy
--   $$\forall A_*\in\mathrm{ONLINE}_{\mathrm{det}}(m,n),\quad \mathbb P_G(A_*(G,\kappa)\in S^h(G,\kappa))\le b_n.$$
--   Then for every jointly measurable randomized online algorithm $A$ with an arbitrary independent seed $\xi\sim\nu$,
--   $$\mathbb P_{\xi,G}(A(\xi,G,\kappa)\in S^h(G,\kappa))\le b_n.$$
--   The conclusion has the same bound with no slack, and it averages over the seed. The deterministic bound is the sole substantive premise. This transfers the uniform deterministic theorem to all randomization allowed by Definition 2.3.
--
--   Differences from the source:
--   - encoding: probability over Gaussian inputs and internal randomness → product Gaussian and arbitrary independent seed laws with jointly measurable online sections; reason: this represents the full measurable randomized class and averages over the seed
--   - encoding: success for ONLINE(n), with its event specified in (A.60) → the same isolated-solution event with m, n, kappa and h explicit; reason: the proof fixes these data before the deterministic success bound
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma A.6, Eqs. (A.60)-(A.61), printed p.24, PDF p.26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_RandomizedOnline
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

universe u
/-- Lemma A.6, printed p.24 / PDF p.26, specialized to its success event from (A.60).
The deterministic premise precedes and entails the randomized bound without slack. -/
theorem lemma_A_6 (m n : ℕ) (κ h bₙ : ℝ)
    (hbound : ∀ A : Fin n → (Fin m × Fin n → ℝ) → ℝ,
      ABPOnline.IsOnlineAlg m n A → detSuccess A κ h ≤ bₙ) :
    ∀ {Ξ : Type u} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
      (A : Ξ → Fin n → (Fin m × Fin n → ℝ) → ℝ),
      IsRandomizedOnline A → randomSuccess ν A κ h ≤ bₙ := by sorry

end OnlinePerceptronIsolation.Binary
