-- Prove2me | Theorems.Thm_OmniMix_Supplement_theorem_1_3
-- name    : OmniMix.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:38:14.810921+00:00
-- url     : https://prove2.me/theorems/af94131f-1644-496a-9e64-d68181782066
-- title:
--   Theorem 1.3 — every forecaster has $\mathbb E[\mathrm{Reg}]\ge\Omega(T^{1/3}/\beta)$ for some bounded $2/\beta$-Lipschitz ($\beta$-mixable) proper loss
-- statement:
--   Let $X=[0,1]^2$. There are an absolute constant $c>0$ and two distinct linear predictors $f_1,f_2:X\to[0,1]$, $f_i(x)=a_ix_1+b_ix_2$, with the following property. For every online forecaster, every $\beta>0$ and every horizon $T$ there exist a context–outcome sequence $(x_1,y_1),\dots,(x_T,y_T)$ and a bounded proper loss $\ell$ that is $2/\beta$-Lipschitz, and hence $\beta$-mixable, such that, with $F=\{f_1,f_2\}$,
--   $$
--   \mathbb E\big[\mathrm{Reg}_{\ell,F}(T)\big]\ \ge\ c\,\frac{T^{1/3}}{\beta}.
--   $$
--
--   Together with Theorem 1.2 this shows that $T^{1/3}/\beta$ is the optimal rate for omniprediction over all mixable proper losses, even when only Lipschitz proper losses are considered, and separates this class from finite classes of mixable losses, for which constant regret is possible.
--
--   **Formalization Note** Forecasts are arbitrary Borel probability measures on $[0,1]$; randomized forecasters are covered by seed averaging, as in Theorem 1.1. Properness, the Lipschitz property and mixability are the base mission's definitions applied to the real-valued loss.
--
--   Differences from the source:
--   - reading: E[Reg] ≥ Ω(T^{1/3}/β) → ∃ c > 0, chosen before the benchmark class, the forecaster, β and T, with c·T^{1/3}/β ≤ Reg; reason: Ω hides an absolute constant; the proof gives c = 1/1000 (L·T^{1/3}/2000 with L = 2/β)
--   - encoding: every (possibly randomized) online forecaster, E[Reg] → every deterministic forecaster with arbitrary Borel probability measures on [0,1] as forecasts, regret without outer expectation; reason: on a fixed sequence E_seed[Reg] is the regret of the seed-averaged forecaster, again such a forecaster
--   - encoding: a 2/β-Lipschitz (hence also β-mixable) bounded proper loss → a real-valued ℓ with |ℓ| ≤ B for some B, IsProper, IsLipschitzLoss (2/β) and IsMixable β of its extended-real coercion; reason: a Lipschitz loss is real-valued; the "hence β-mixable" is part of the claim and kept as a conjunct
--   - encoding: X = [0,1]², linear predictors in [0,1]^X, rounds 1..T → unitInterval × unitInterval, maps into unitInterval with f(x) = a·x₁ + b·x₂, rounds Fin T; reason: Lean convention; same objects
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Theorem 1.3, p.3 (PDF p.5); restated with proof App. A.2, pp.21–24 (PDF pp.23–26)

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable
import Definitions.Def_OmniMix_IsLipschitzLoss
import Definitions.Def_OmniMix_Supplement_MeasForecaster
import Definitions.Def_OmniMix_Supplement_measForecasts
import Definitions.Def_OmniMix_Supplement_seqRegret

namespace OmniMix.Supplement

open OmniMix

open scoped Classical in
/-- **Theorem 1.3 (the `T^{1/3}/β` rate is optimal).** Liu–Luo–Ratliff, arXiv:2610.41023, §1.1, p.3
(restated with proof in App. A.2, pp.21–24): "There exists a fixed benchmark class `F ⊆ [0, 1]^X` of
two linear predictors for `X = [0, 1]^2` such that, for every online forecaster, every `β > 0`, and
every `T`, there exist a sequence of context-outcome pairs `(x_1, y_1), …, (x_T, y_T)` and a
`2/β`-Lipschitz (hence also β-mixable) bounded proper loss such that
`E[Reg_{ℓ,F}(T)] ≥ Ω(T^{1/3}/β)`."

There are an absolute constant `c > 0` and two distinct linear maps `f₁, f₂ : [0,1]² → [0,1]` such
that for every horizon `T`, every measure-valued online forecaster `A` and every `β > 0` there are
contexts `x`, outcomes `y` and a bounded real-valued loss `ℓ` that is proper, `2/β`-Lipschitz and
β-mixable, whose regret against `{f₁, f₂}` is at least `c·T^{1/3}/β`.

**Formalization Note.** `X = [0,1]²` is `unitInterval × unitInterval`; "linear" is
`f(x) = a·x₁ + b·x₂`. `Ω(·)` is read as `c·(·)` with `c` absolute, chosen before the benchmark class,
the forecaster, `β` and `T` (the proof gives `c = 1/1000`). Forecasts are arbitrary Borel
probability measures on `[0,1]` (`MeasForecaster`; seed averaging covers randomized forecasters).
The properness, Lipschitz and mixability predicates are the base ones applied to the `EReal`
coercion of `ℓ`; "(hence also β-mixable)" is kept as a conjunct. The regret uses `π_ℓ = id`. -/
theorem theorem_1_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ f₁ f₂ : unitInterval × unitInterval → unitInterval, f₁ ≠ f₂ ∧
      (∃ a b : ℝ, ∀ x, (f₁ x : ℝ) = a * (x.1 : ℝ) + b * (x.2 : ℝ)) ∧
      (∃ a b : ℝ, ∀ x, (f₂ x : ℝ) = a * (x.1 : ℝ) + b * (x.2 : ℝ)) ∧
      ∀ (T : ℕ) (A : MeasForecaster (unitInterval × unitInterval) T) (β : ℝ), 0 < β →
        ∃ (x : Fin T → unitInterval × unitInterval) (y : Fin T → Bool)
          (ℓ : unitInterval → Bool → ℝ),
          (∃ B : ℝ, ∀ p b, |ℓ p b| ≤ B) ∧
          IsProper (fun p b => ((ℓ p b : ℝ) : EReal)) ∧
          IsLipschitzLoss (2 / β) (fun p b => ((ℓ p b : ℝ) : EReal)) ∧
          IsMixable β (fun p b => ((ℓ p b : ℝ) : EReal)) ∧
          ((c * (T : ℝ) ^ (1 / 3 : ℝ) / β : ℝ) : EReal) ≤
            seqRegret ℓ {f₁, f₂} x y (measForecasts A x y) := by sorry

end OmniMix.Supplement
