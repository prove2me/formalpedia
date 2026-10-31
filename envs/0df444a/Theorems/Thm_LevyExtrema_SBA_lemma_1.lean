-- Prove2me | Theorems.Thm_LevyExtrema_SBA_lemma_1
-- name    : LevyExtrema.SBA.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:53.883469+00:00
-- url     : https://prove2.me/theorems/449f5356-1e99-4223-b8ea-3a2b7083cf63
-- title:
--   Lemma 1 — bounds (4.7)–(4.9) on the Lévy measure, for every exponent $b\in[0,2]$ with $I^b_0<\infty$
-- statement:
--   Let $\nu$ be a Lévy measure, let $b\in[0,2]$ with $I^b_0=\int_{(-1,1)}|x|^b\nu(dx)<\infty$, and let $\kappa\in(0,1]$. Then
--
--   1. $\overline\nu(\kappa)=\nu(\mathbb R\setminus(-\kappa,\kappa))\le\kappa^{-b}I^b_0+\overline\nu(1)$;
--   2. $\overline\sigma^2(\kappa)=\int_{(-\kappa,\kappa)}x^2\nu(dx)\le\kappa^{2-b}I^b_0$;
--   3. for every $p\in\mathbb R$, $\displaystyle\int_{(-1,-\kappa]\cup[\kappa,1)}|x|^p\nu(dx)\le\kappa^{-(b-p)^+}I^b_0$;
--   4. for every $p\ge b$, $\displaystyle\int_{(-\kappa,\kappa)}|x|^p\nu(dx)\le\kappa^{p-b}I^b_0$.
--
--   The paper states the lemma for $b=\beta_+$ (4.6), which satisfies $\beta_+\in[0,2]$ and $I^{\beta_+}_0<\infty$. The bounds control the small and large jumps after a truncation at level $\kappa$, and are used in the proof of Lemma 2 with $\kappa=(t/T)^{1/\beta_+}$.
--
--   Differences from the source:
--   - generalization: the exponent β₊ of (4.6) → every b ∈ [0, 2] with I^b_0 < ∞; reason: β₊ (as printed, including β₊ = 0, and as corrected) satisfies both conditions, so the source's lemma is the case b = β₊; no correction is needed
--   - encoding: integrals against ν → lintegrals in ℝ≥0∞ (ENNReal.ofReal of the integrand); reason: the integrands are nonnegative; no bound holds by a junk value
--   - encoding: the Lévy measure ν of X → Tr.levyMeasure of a triplet with Tr.IsLevy; no process appears; reason: the Lévy measures of Lévy processes are exactly the measures allowed by Tr.IsLevy; same instances
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, Lemma 1, (4.7)–(4.9), p. 21

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_LevyMeasureIntegrals

open MeasureTheory
open scoped ENNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Lemma 1 — bounds on the Lévy measure** (for every admissible exponent b).
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, Lemma 1, p. 21: "The Lévy measure ν
of X satisfies the following for all κ ∈ (0, 1]: (4.7) ν̄(κ) = ν(R \ (−κ, κ)) ≤ κ^{−β₊}I^{β₊}_0 +
ν̄(1), σ̄²(κ) = ∫_{(−κ,κ)} x²ν(dx) ≤ κ^{2−β₊}I^{β₊}_0. Moreover the following inequalities hold:
(4.8) ∫_{(−1,−κ]∪[κ,1)} |x|^pν(dx) ≤ κ^{−(β₊−p)^+}I^{β₊}_0, for p ∈ R, (4.9) ∫_{(−κ,κ)}
|x|^pν(dx) ≤ κ^{p−β₊}I^{β₊}_0, for p ≥ β₊."

Stated for every exponent `b ∈ [0, 2]` with `I^b_0 < ∞` in place of `β₊`.

**Formalization Note.** The integrals are lintegrals (`ℝ≥0∞`), so no bound holds by a junk value.
The paper's β₊ (as printed, and as corrected in `betaPlus`) satisfies `0 ≤ β₊ ≤ 2` and
`I^{β₊}_0 < ∞`, so the paper's Lemma 1 is the instance `b = β₊`. -/
theorem lemma_1 (Tr : Triplet) (hTr : Tr.IsLevy) (b : ℝ) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hIb : I0 Tr b < ⊤) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    Tr.levyMeasure (Set.Ioo (-κ) κ)ᶜ
        ≤ ENNReal.ofReal (κ ^ (-b)) * I0 Tr b + Tr.levyMeasure (Set.Ioo (-1) 1)ᶜ ∧
    ∫⁻ x in Set.Ioo (-κ) κ, ENNReal.ofReal (x ^ 2) ∂Tr.levyMeasure
        ≤ ENNReal.ofReal (κ ^ (2 - b)) * I0 Tr b ∧
    (∀ p : ℝ, ∫⁻ x in Set.Ioc (-1) (-κ) ∪ Set.Ico κ 1, ENNReal.ofReal (|x| ^ p) ∂Tr.levyMeasure
        ≤ ENNReal.ofReal (κ ^ (-(max (b - p) 0))) * I0 Tr b) ∧
    (∀ p : ℝ, b ≤ p → ∫⁻ x in Set.Ioo (-κ) κ, ENNReal.ofReal (|x| ^ p) ∂Tr.levyMeasure
        ≤ ENNReal.ofReal (κ ^ (p - b)) * I0 Tr b) := by sorry

end LevyExtrema.SBA
