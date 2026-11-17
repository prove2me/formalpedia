-- Prove2me | Theorems.Thm_OmniMix_Supplement_theorem_3_3
-- name    : OmniMix.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:39:56.428379+00:00
-- url     : https://prove2.me/theorems/5f7e0b00-e623-443f-9575-36dd2c5a045f
-- title:
--   Theorem 3.3 — Algorithm 1 has $O(L(T^{1/3}(\log|F|)^{2/3}+\log|F|))$ regret for every proper $L$-Lipschitz loss
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $F$ be a finite class of maps $X\to[0,1]$ with $|F|\ge2$, let $T\ge1$, and run Algorithm 1 with learning rate
--   $$
--   \eta=\min\Big\{\frac12,\Big(\frac{\log|F|}{T}\Big)^{1/3}\Big\}
--   $$
--   on any context–outcome sequence, with any EVI solver. Then for every $L$ and every proper $L$-Lipschitz loss $\ell$,
--   $$
--   \mathrm{Reg}_{\ell,F}(T)\le C\,L\,\Big(T^{1/3}(\log|F|)^{2/3}+\log|F|\Big).
--   $$
--
--   The learning rate does not depend on $L$, so one run serves all Lipschitz proper losses at once. By Theorem 1.3 the rate $LT^{1/3}$ is optimal for this class in the contextual setting.
--
--   **Formalization Note** A run of Algorithm 1 is any sequence of probability measures on $[0,1]$ that meets the EVI condition of every round. Lipschitz losses are real-valued; properness and the Lipschitz property are the base mission's definitions.
--
--   Differences from the source:
--   - reading: Reg = O(L(T^{1/3}(log|F|)^{2/3} + log|F|)) → ∃ absolute C > 0, chosen first, with Reg ≤ C·L·(T^{1/3}(log|F|)^{2/3} + log|F|); reason: O hides an absolute constant (explicit through Lemmas 3.1–3.2)
--   - encoding: Algorithm 1's input constraint 0 < η ≤ 1/2 for η = min{1/2, (log|F|/T)^{1/3}} → hypotheses |F| ≥ 2 and T ≥ 1; reason: for this η, 0 < η holds exactly when |F| ≥ 2 and T ≥ 1 (η = 0 at |F| = 1; T = 0 has no rounds and divides by 0)
--   - encoding: "Algorithm 1 ensures" → for every sequence of forecast probability measures on [0,1] meeting the EVI condition in every round (any EVI solver); reason: Algorithm 1 takes an arbitrary EVI solver as input
--   - encoding: a proper L-Lipschitz loss → a real-valued ℓ whose extended-real coercion satisfies the base IsProper and IsLipschitzLoss L; reason: a Lipschitz loss is real-valued; same losses
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Theorem 3.3, p.13 (PDF p.15); Algorithm 1, p.11 (PDF p.13); Lemmas 3.1–3.2, pp.11–12

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsLipschitzLoss
import Definitions.Def_OmniMix_Supplement_IsAlg1Run
import Definitions.Def_OmniMix_Supplement_seqRegret

namespace OmniMix.Supplement

open OmniMix

universe u

/-- **Theorem 3.3 (Algorithm 1 for all Lipschitz proper losses).** Liu–Luo–Ratliff,
arXiv:2610.41023, §3.1, p.13: "With `η = min{1/2, (log |F|/T)^{1/3}}`, Algorithm 1 ensures that for any
proper and L-Lipschitz loss `ℓ`, `Reg_{ℓ,F}(T) = O(L(T^{1/3}(log |F|)^{2/3} + log |F|))`."

There is an absolute constant `C > 0` such that for every finite benchmark class `F` with `|F| ≥ 2`,
every horizon `T ≥ 1`, every context–outcome sequence and every run `D` of Algorithm 1 on it with
`η = min{1/2, (log|F|/T)^{1/3}}`, every `L` and every proper `L`-Lipschitz loss `ℓ` satisfy
`Reg_{ℓ,F}(T) ≤ C·L·(T^{1/3}(log|F|)^{2/3} + log|F|)`.

**Formalization Note.** `|F| ≥ 2` and `T ≥ 1` are Algorithm 1's input constraint `0 < η ≤ 1/2`
for the given `η` (at `|F| = 1` it is `0`). A run is any sequence of forecast probability measures on
`[0,1]` meeting the EVI condition of every round (`IsAlg1Run`); `η` does not depend on `L`, and the
bound holds for all proper Lipschitz losses at once. A Lipschitz loss is real-valued (the base
`IsLipschitzLoss` requires it), so `ℓ` is taken real-valued and the base predicates are applied to
its `EReal` coercion; the regret uses `π_ℓ = id`. -/
theorem theorem_3_3 : ∃ C : ℝ, 0 < C ∧ ∀ {X : Type u} (F : Finset (X → unitInterval)) (T : ℕ),
    2 ≤ F.card → 1 ≤ T → ∀ (x : Fin T → X) (y : Fin T → Bool)
    (D : Fin T → MeasureTheory.ProbabilityMeasure unitInterval),
    IsAlg1Run F T (min (1 / 2) ((Real.log (F.card : ℝ) / (T : ℝ)) ^ (1 / 3 : ℝ))) x y D →
    ∀ (L : ℝ) (ℓ : unitInterval → Bool → ℝ), IsProper (fun p b => ((ℓ p b : ℝ) : EReal)) →
      IsLipschitzLoss L (fun p b => ((ℓ p b : ℝ) : EReal)) →
      seqRegret ℓ F x y D ≤ ((C * L * ((T : ℝ) ^ (1 / 3 : ℝ) *
        Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) + Real.log (F.card : ℝ)) : ℝ) : EReal) := by sorry

end OmniMix.Supplement
