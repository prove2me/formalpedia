-- Prove2me | Theorems.Thm_OmniMix_Supplement_theorem_1_4
-- name    : OmniMix.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:39:00.376649+00:00
-- url     : https://prove2.me/theorems/2fef0e21-f286-49d5-ba14-d55395a77491
-- title:
--   Theorem 1.4 — best of all worlds: $O(\log(|F||L_{\rm mix}|)/\beta)$, $\tilde O(T^{1/3}(\log|F|)^{2/3}/\beta)$, $O(\sqrt{T\log(|F||L_{\rm bd}|)})$ at once (corrected: |F| ≥ 2, ℓ finite on (0,1))
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $X$ be a context space, $F$ a finite class of maps $X\to[0,1]$ with $|F|\ge2$, and $T$ a horizon. Let $L_{\mathrm{bd}}$ be a finite class of losses with values in $[0,1]$, each $\ell\in L_{\mathrm{bd}}$ with a Bayes-optimal post-processing map $\pi_\ell$ (so $\pi_\ell(p)$ minimizes $q\mapsto\mathbb E_{Y\sim\mathrm{Ber}(p)}[\ell(q,Y)]$), and let $L_{\mathrm{mix}}$ be a finite class of proper losses $[0,1]\times\{0,1\}\to\mathbb R\cup\{+\infty\}$, each finite on $(0,1)$ and $\beta$-mixable for some $\beta>0$. Then one online forecaster guarantees, for every context–outcome sequence, all of the following simultaneously:
--
--   1. for every $\ell\in L_{\mathrm{mix}}$ and every $\beta>0$ at which $\ell$ is $\beta$-mixable,
--   $$
--   \mathrm{Reg}_{\ell,F}(T)\le C\,\frac{\log(|F|\,|L_{\mathrm{mix}}|)}{\beta};
--   $$
--   2. for every proper loss $\ell$ that is finite on $(0,1)$ (in $L_{\mathrm{mix}}$ or not) and every $\beta>0$ at which it is $\beta$-mixable,
--   $$
--   \mathrm{Reg}_{\ell,F}(T)\le C\,\log(2T+1)\,\frac{T^{1/3}(\log|F|)^{2/3}}{\beta};
--   $$
--   3. for every $\ell\in L_{\mathrm{bd}}$, with the regret of the agent who plays $\pi_\ell(P_t)$,
--   $$
--   \mathrm{Reg}_{\ell,F}(T)\le C\sqrt{T\log(|F|\,|L_{\mathrm{bd}}|)}.
--   $$
--
--   One algorithm thus achieves the constant-in-$T$ guarantee known for finite classes of mixable losses, the optimal $T^{1/3}$ rate of Theorem 1.2 for all mixable proper losses, and the $\sqrt T$ guarantee known for finite classes of bounded losses.
--
--   **Formalization Note** The forecaster has finitely supported forecasts and may depend on $X,F,T,L_{\mathrm{bd}}$, the maps $\pi_\ell$ and $L_{\mathrm{mix}}$; it is fixed before every loss, $\beta$ and sequence.
--
--   Differences from the source:
--   - correction: any finite benchmark class F → |F| ≥ 2; reason: at |F| = 1 clause 2 claims Reg ≤ 0 for log loss (1-mixable, proper, finite on (0,1)); with F = {x ↦ 1/2} this forces every forecast to be δ_{1/2}, and then ℓ₀(q,·) = (0,1) for q < 1/3, (0.6,0.6) for 1/3 ≤ q ≤ 2/3, (1,0) for q > 2/3 with the Bayes selection π(p) = 0 for p ≤ 1/2, 1 otherwise has regret 0.4·T on y ≡ 1, while clause 3's bound with L_bd = {ℓ₀} is 0
--   - correction: every mixable proper loss (in L_mix and in clause 2) → also finite on (0,1); reason: ℓ(q,0) = q, ℓ(q,1) = +∞ and its mirror are proper and β-mixable for every β (bound 0); with F = {0,1} every forecaster has positive regret for one of them on a constant outcome sequence (the base goal's correction)
--   - reading: O(·) and Õ(·) → one absolute C > 0 chosen before everything; Õ(T^{1/3}(log|F|)^{2/3}/β) as C·log(2T+1)·T^{1/3}(log|F|)^{2/3}/β; reason: footnote 1 (Õ hides polylog factors in T); the base goal's reading, log(2T+1) = M_δ/2 being the proof's factor
--   - reading: 1/β⋆_ℓ → 1/β for every β > 0 at which ℓ is β-mixable; reason: at β = β⋆_ℓ this is the paper's bound; needs no attainment of the supremum and covers β⋆_ℓ = +∞
--   - encoding: π_ℓ(p) = argmin_q E_{Y∼Ber(p)} ℓ(q,Y), ties broken in a fixed way → a given map π ℓ with the hypothesis that π ℓ p minimises the Bernoulli-expected loss, fixed before the forecaster; reason: an argmin need not exist for an arbitrary bounded loss; the paper fixes the tie rule in advance
--   - encoding: loss codomain ℝ ∪ {+∞}; forecasts any distribution → EReal-valued losses never −∞; finitely supported forecasts; reason: same losses; restricting the forecaster makes the existence claim stronger
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Theorem 1.4, p.3 (PDF p.5); restated with proof App. A.4, pp.24–27 (PDF pp.26–29); Algorithm 3, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable
import Definitions.Def_OmniMix_bern
import Definitions.Def_OmniMix_regret
import Definitions.Def_OmniMix_Supplement_regretPost

namespace OmniMix.Supplement

open OmniMix

universe u

/-- **Theorem 1.4 (a best-of-all-worlds forecaster).** Liu–Luo–Ratliff, arXiv:2610.41023, §1.1, p.3
(restated with proof in App. A.4, pp.24–27; Algorithm 3, p.18): "For any fixed finite class `L_bd`
of losses with bounded range `[0, 1]` and any fixed finite class of mixable proper losses `L_mix`,
there exists an online forecaster (Algorithm 3) that guarantees all of the following
simultaneously: 1. for every `ℓ ∈ L_mix`, `Reg_{ℓ,F}(T) = O(log(|F||L_mix|)/β⋆_ℓ)`; 2. for every
mixable proper loss `ℓ` (whether or not it belongs to `L_mix`),
`Reg_{ℓ,F}(T) = Õ(T^{1/3}(log |F|)^{2/3}/β⋆_ℓ)`; 3. for every `ℓ ∈ L_bd`,
`Reg_{ℓ,F}(T) = O(√(T log(|F||L_bd|)))`."

There is an absolute constant `C > 0` such that for every context type `X`, every finite benchmark
class `F` with `|F| ≥ 2`, every horizon `T`, every finite class `L_bd` of `[0,1]`-valued losses with
Bayes selections `π ℓ`, and every finite class `L_mix` of proper losses that are never `−∞`, finite
on `(0,1)` and mixable, one forecaster `A` satisfies all three bounds, for every sequence:
1. `Reg_{ℓ,F}(T) ≤ C·log(|F||L_mix|)/β` for `ℓ ∈ L_mix` and every `β > 0` at which ℓ is β-mixable;
2. `Reg_{ℓ,F}(T) ≤ C·log(2T+1)·T^{1/3}(log|F|)^{2/3}/β` for every proper, never `−∞`, finite-on-`(0,1)`,
   β-mixable `ℓ`;
3. `Reg_{ℓ,F}(T) ≤ C·√(T·log(|F||L_bd|))` for `ℓ ∈ L_bd`, the regret using `π ℓ`.

**Formalization Note.** Corrections: `|F| ≥ 2` (at `|F| = 1` clause 2 claims `Reg ≤ 0` for log loss,
forcing every forecast to be `δ_{1/2}` when `F = {x ↦ 1/2}`, and then a non-proper `[0,1]`-valued
loss in `L_bd` has regret `0.4·T` while clause 3's bound is `0`); mixable losses finite on `(0,1)`
(the base goal's correction). `Õ` is read as `C·log(2T+1)`, as in the base goal; `1/β⋆_ℓ` is read as
`1/β` for every `β > 0` at which `ℓ` is β-mixable. The Bayes selection `π ℓ` (the paper's `π_ℓ`, ties
broken in a fixed way) is data with the optimality hypothesis, since an argmin need not exist for
an arbitrary bounded loss. The forecaster may depend on `X, F, T, L_bd, π, L_mix` and is chosen
before every loss, `β` and sequence. Forecasts are finitely supported (an existential over this
subclass is the stronger claim). -/
theorem theorem_1_4 : ∃ C : ℝ, 0 < C ∧ ∀ (X : Type u) (F : Finset (X → unitInterval)) (T : ℕ),
    2 ≤ F.card → ∀ (Lbd : Finset Loss) (π : Loss → unitInterval → unitInterval),
    (∀ ℓ ∈ Lbd, ∀ p y, 0 ≤ ℓ p y ∧ ℓ p y ≤ 1) →
    (∀ ℓ ∈ Lbd, ∀ p q : unitInterval, bern p (ℓ (π ℓ p)) ≤ bern p (ℓ q)) →
    ∀ Lmix : Finset Loss,
    (∀ ℓ ∈ Lmix, IsProper ℓ ∧ (∀ p y, ℓ p y ≠ ⊥) ∧
      (∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) ∧
      ∃ β : ℝ, 0 < β ∧ IsMixable β ℓ) →
    ∃ A : Forecaster X T,
      (∀ ℓ ∈ Lmix, ∀ β : ℝ, 0 < β → IsMixable β ℓ → ∀ (x : Fin T → X) (y : Fin T → Bool),
        regret ℓ F A x y ≤
          ((C * Real.log ((F.card : ℝ) * (Lmix.card : ℝ)) / β : ℝ) : EReal)) ∧
      (∀ (ℓ : Loss) (β : ℝ), 0 < β → IsProper ℓ → (∀ p y, ℓ p y ≠ ⊥) →
        (∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) →
        IsMixable β ℓ → ∀ (x : Fin T → X) (y : Fin T → Bool),
        regret ℓ F A x y ≤ ((C * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) / β : ℝ) : EReal)) ∧
      (∀ ℓ ∈ Lbd, ∀ (x : Fin T → X) (y : Fin T → Bool),
        regretPost ℓ (π ℓ) F A x y ≤
          ((C * Real.sqrt ((T : ℝ) * Real.log ((F.card : ℝ) * (Lbd.card : ℝ))) : ℝ) : EReal)) := by sorry

end OmniMix.Supplement
