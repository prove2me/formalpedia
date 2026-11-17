-- Prove2me | Theorems.Thm_OmniMix_Supplement_theorem_1_1
-- name    : OmniMix.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:37:36.087835+00:00
-- url     : https://prove2.me/theorems/9737738f-6a9e-4a46-83ee-5f5b69e22e1e
-- title:
--   Theorem 1.1 — no forecaster has sublinear regret for all bounded proper losses, even against two affine predictors ($\mathbb E[\mathrm{Reg}]\ge T/12$)
-- statement:
--   Let $X=[0,3/4]$. There are two distinct affine predictors $f_1,f_2:X\to[0,1]$, $f_i(x)=a_ix+b_i$, with the following property. For every horizon $T$ and every online forecaster there exist a context–outcome sequence $(x_1,y_1),\dots,(x_T,y_T)$ and a proper loss $\ell:[0,1]\times\{0,1\}\to[0,1]$ such that, with $F=\{f_1,f_2\}$,
--   $$
--   \mathbb E\big[\mathrm{Reg}_{\ell,F}(T)\big]\ \ge\ \frac T{12}.
--   $$
--   Here $\mathrm{Reg}_{\ell,F}(T)=\sum_t\mathbb E_{P\sim D_t}[\ell(P,y_t)]-\min_{f\in F}\sum_t\ell(f(x_t),y_t)$, and the outer expectation is over the forecaster's own randomness.
--
--   The sequence and the loss may depend on the forecaster; the benchmark class may not. So omniprediction with sublinear regret for the whole class of bounded proper losses is impossible in the contextual setting, in contrast with the non-contextual case, where $O(\sqrt T)$ is achievable.
--
--   **Formalization Note** A forecaster maps the history and the current context to an arbitrary Borel probability measure on $[0,1]$. Randomized forecasters are covered: on a fixed sequence the expected regret over the forecaster's seed equals the regret of the seed-averaged forecaster. The witness loss is required to be measurable in the prediction, so that the expectation is defined.
--
--   Differences from the source:
--   - encoding: every (possibly randomized) online forecaster, E[Reg] → every deterministic forecaster whose forecasts are arbitrary Borel probability measures on [0,1], regret without outer expectation; reason: on a fixed sequence E_seed[Reg] is the regret of the seed-averaged forecaster D̄_t = E_seed D_t, again such a forecaster, so the two claims are equivalent
--   - encoding: a proper loss with range [0,1] → a real-valued loss with values in [0,1], measurable in p for each outcome, proper as an extended-real loss; reason: range [0,1] means real values; measurability is presupposed by E_{P∼D_t}, and the paper's witnesses (V-shaped losses) are measurable
--   - encoding: X = [0,3/4], affine predictors in [0,1]^X, rounds 1..T → the subtype Set.Icc 0 (3/4), maps into unitInterval with f(x) = a·x + b, rounds Fin T; reason: Lean convention; same objects
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Theorem 1.1, p.2 (PDF p.4); restated with proof App. A.1, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_Supplement_MeasForecaster
import Definitions.Def_OmniMix_Supplement_measForecasts
import Definitions.Def_OmniMix_Supplement_seqRegret

namespace OmniMix.Supplement

open OmniMix

open scoped Classical in
/-- **Theorem 1.1 (impossibility for all bounded proper losses).** Liu–Luo–Ratliff,
arXiv:2610.41023, §1.1, p.2 (restated with proof in App. A.1, pp.20–21): "There exists a fixed
benchmark class `F ⊆ [0, 1]^X` of two affine predictors for `X = [0, 3/4]` such that, for every
online forecaster and every horizon `T`, there exist a sequence of context-outcome pairs
`(x_1, y_1), …, (x_T, y_T)` and a proper loss with range `[0, 1]` such that `E[Reg_{ℓ,F}(T)] ≥ T/12`."

There are two distinct affine maps `f₁, f₂ : [0,3/4] → [0,1]` such that for every horizon `T` and
every measure-valued online forecaster `A` there are contexts `x`, outcomes `y` and a loss `ℓ` with
values in `[0,1]`, measurable in the prediction and proper, whose regret against `{f₁, f₂}` is at
least `T/12`.

**Formalization Note.** `X = [0,3/4]` is the subtype `Set.Icc 0 (3/4)` of `ℝ`; "affine" is
`f(x) = a·x + b`. Forecasts are arbitrary Borel probability measures on `[0,1]` (`MeasForecaster`);
the paper's outer expectation over the forecaster's own randomness is covered by seed averaging
(see `MeasForecaster`), so quantifying over deterministic measure-valued forecasters is the
paper's claim. The loss is real-valued (an existential over real-valued losses is at least as
strong as over `ℝ ∪ {+∞}`-valued ones); properness is the base `IsProper` of its `EReal` coercion;
its regret uses `π_ℓ = id` (p.21). Measurability in `p` makes the expectation meaningful. -/
theorem theorem_1_1 :
    ∃ f₁ f₂ : Set.Icc (0 : ℝ) (3 / 4) → unitInterval, f₁ ≠ f₂ ∧
      (∃ a b : ℝ, ∀ x, (f₁ x : ℝ) = a * (x : ℝ) + b) ∧
      (∃ a b : ℝ, ∀ x, (f₂ x : ℝ) = a * (x : ℝ) + b) ∧
      ∀ (T : ℕ) (A : MeasForecaster (Set.Icc (0 : ℝ) (3 / 4)) T),
        ∃ (x : Fin T → Set.Icc (0 : ℝ) (3 / 4)) (y : Fin T → Bool) (ℓ : unitInterval → Bool → ℝ),
          (∀ b : Bool, Measurable fun p => ℓ p b) ∧ (∀ p b, 0 ≤ ℓ p b ∧ ℓ p b ≤ 1) ∧
          IsProper (fun p b => ((ℓ p b : ℝ) : EReal)) ∧
          (((T : ℝ) / 12 : ℝ) : EReal) ≤ seqRegret ℓ {f₁, f₂} x y (measForecasts A x y) := by sorry

end OmniMix.Supplement
