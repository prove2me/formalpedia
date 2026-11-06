-- Prove2me | Theorems.Thm_OmniMix_theorem_1_2
-- name    : OmniMix.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:42:32.891532+00:00
-- url     : https://prove2.me/theorems/93f4bbff-cd46-4b93-85cf-1e1b0a6559e2
-- title:
--   Theorem 1.2 — one forecaster with $\tilde O(T^{1/3}(\log|F|)^{2/3}/\beta)$ regret for every mixable proper loss (corrected: ℓ finite on (0,1))
-- statement:
--   There is an absolute constant $K>0$ with the following property. For every context space $X$, every finite benchmark class $F$ of maps $X\to[0,1]$ and every horizon $T\in\mathbb N$, there is one online forecaster such that for every loss $\ell:[0,1]\times\{0,1\}\to\mathbb R\cup\{+\infty\}$ that is proper, finite on $(0,1)$ and $\beta$-mixable for some $\beta>0$, and for every context–outcome sequence $(x_1,y_1),\dots,(x_T,y_T)$,
--   $$
--   \mathrm{Reg}_{\ell,F}(T)\le K\,\log(2T+1)\,\frac{T^{1/3}(\log|F|)^{2/3}}{\beta}.
--   $$
--
--   The forecaster is fixed before the loss: the same forecasts serve every mixable proper loss simultaneously, with the rate of each loss governed by its own mixability constant. By Theorem 1.3 of the paper the rate $T^{1/3}/\beta$ cannot be improved, even for Lipschitz proper losses.
--
--   Differences from the source:
--   - correction: every mixable proper loss → ℓ also finite on (0,1); reason: ℓ(q,0) = q, ℓ(q,1) = +∞ and its mirror ℓ'(q,1) = 1 − q, ℓ'(q,0) = +∞ are proper and β-mixable for every β (β⋆ = +∞, bound 0); with F = {0,1} every forecaster has positive regret for one of them on a constant outcome sequence
--   - reading: Õ(·), suppressing log T factors → K·log(2T+1)·(·) with K absolute; reason: log(2T+1) = M_δ/2 is the proof's own factor and gives (27) when log|F| ≤ T; a literal log T would claim regret ≤ 0 at T = 1, false for squared loss with F = {0.2, 0.8}
--   - reading: 1/β⋆_ℓ → 1/β for every β > 0 at which ℓ is β-mixable; reason: at β = β⋆_ℓ this is the paper's bound; it needs no attainment of the supremum
--   - encoding: D_t any distribution over [0,1]; regret in ℝ∪{+∞} → D_t finitely supported; regret in ℝ∪{±∞} with a − (+∞) = −∞; reason: restricting forecasts makes the existence claim stronger; −∞ is the paper's convention for an infinite comparator loss
--   - encoding: loss codomain ℝ ∪ {+∞} → EReal-valued loss with ℓ(p,y) ≠ −∞ assumed; reason: EReal contains ℝ ∪ {+∞}; same instances
--   - generalization: finite benchmark class F → finite F, possibly empty; reason: for empty F the infimum is +∞ and the regret is −∞, so the claim for nonempty F is the paper's
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Theorem 1.2, p.3 (PDF p.5); restated with proof App. A.3, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable
import Definitions.Def_OmniMix_regret

namespace OmniMix

universe u

/-- **Theorem 1.2 (optimal omniprediction for all mixable proper losses).** Liu–Luo–Ratliff, arXiv:2610.41023, §1.1, p.3
(restated with proof in App. A.3, p.24): "There exists an online forecaster (Algorithm 2) such that for
every mixable proper loss `ℓ`, `Reg_{ℓ,F}(T) = Õ(T^{1/3}(log |F|)^{2/3}/β⋆_ℓ)` (1) where `Õ(·)`
suppresses dependence on log T factors."

There is an absolute constant `K > 0` such that for every context type `X`, every finite benchmark
class `F ⊆ [0,1]^X` and every horizon `T`, one forecaster `A` satisfies, for every proper loss `ℓ`
that is never `−∞`, finite on `(0,1)` and β-mixable for some `β > 0`, and every context–outcome
sequence,
`Reg_{ℓ,F}(T) ≤ K·log(2T+1)·T^{1/3}·(log|F|)^{2/3}/β`.

**Formalization Note.** Correction: `ℓ` finite on `(0,1)`. As printed the theorem fails for
`ℓ(q,0) = q`, `ℓ(q,1) = +∞` (proper and β-mixable for every β, so `β⋆ = +∞`) together with its mirror:
with `F = {0, 1}` every forecaster has positive regret for one of them on a constant outcome
sequence, while the bound is `0`. `Õ` is read as `K·log(2T+1)` with `K` absolute (`log(2T+1) = M_δ/2`;
a literal `log T` would claim `Reg ≤ 0` at `T = 1`). `1/β⋆_ℓ` is read as `1/β` for every `β` at which
`ℓ` is β-mixable. The forecaster is chosen after `X`, `F`, `T` and before the loss and the sequence.
Forecasts are finitely supported. `F` may be empty (then the regret is `−∞`). -/
theorem theorem_1_2 : ∃ K : ℝ, 0 < K ∧ ∀ (X : Type u) (F : Finset (X → unitInterval)) (T : ℕ),
    ∃ A : Forecaster X T, ∀ (ℓ : Loss) (β : ℝ), 0 < β → IsProper ℓ →
      (∀ p y, ℓ p y ≠ ⊥) → (∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) →
      IsMixable β ℓ → ∀ (x : Fin T → X) (y : Fin T → Bool),
        regret ℓ F A x y ≤ ((K * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) / β : ℝ) : EReal) := by sorry

end OmniMix
