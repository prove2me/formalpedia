-- Prove2me | Theorems.Thm_OptHedgeGames_lemma_5_5
-- name    : OptHedgeGames.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:15.92283+00:00
-- url     : https://prove2.me/theorems/b65124df-78e2-4b1b-afc0-f5e1bcea57f7
-- title:
--   Lemma 5.5 — discrete–continuous comparisons
-- statement:
--   In the two-player run with $0<\eta\le1/100$, for every horizon $T\ge1$,
--   $$
--   \sum_{t=1}^T\mathrm{Var}_{x_1^t}(\ell_1^t-\ell_1^{t-1})\le\frac14+e^{3\eta}\int_1^T\mathrm{Var}_{x_1^{\lfloor s\rfloor}}(L'(s))\,ds
--   $$
--   and
--   $$
--   \int_1^T\mathrm{Var}_{x_1^{\lfloor s\rfloor}}(L(s))\,ds\le2\sum_{t=1}^T\mathrm{Var}_{x_1^t}(\ell_1^t)+2\int_1^T\mathrm{Var}_{x_1^{\lfloor s\rfloor}}(L'(s))\,ds.
--   $$
--   These inequalities pass between the discrete variances of the regret analysis and the energies of the interpolation.
--
--   Differences from the source:
--   - generalization: n ≥ 2 actions (Setting and notation of §5, p.18) → n ≥ 1; reason: at n = 1 every variance vanishes and the claim still holds; n ≥ 2 is an instance
--   - generalization: standing assumption of §5.3: W ≥ 1 and 0 < ηW ≤ 10⁻³, in particular η ≤ 1/100 → 0 < η ≤ 1/100, no W; reason: the lemma does not mention W and its proof uses only η ≤ 1/100, through Lemma 5.1; every η of the source is an instance
--   - encoding: the horizon T, a number of rounds (§2, p.4; Theorem 3.4 says T ≥ 1) → 1 ≤ T; reason: T = 0 is no horizon; the source's horizon is a positive number of rounds
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Lemma 5.5, (40), (41), p.22

import Mathlib
import Definitions.Def_OptHedgeGames_Interpolation

namespace OptHedgeGames

/-- **Lemma 5.5** (discrete–continuous comparisons; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Lemma 5.5, p.22). For every horizon `T`,
`Σ_{t=1}^T Var_{xᵗ₁}(ℓᵗ₁ − ℓᵗ⁻¹₁) ≤ 1/4 + e^{3η} ∫_1^T Var_{x₁^{⌊s⌋}}(L′(s)) ds`, which is (40), and
`∫_1^T Var_{x₁^{⌊s⌋}}(L(s)) ds ≤ 2 Σ_{t=1}^T Var_{xᵗ₁}(ℓᵗ₁) + 2 ∫_1^T Var_{x₁^{⌊s⌋}}(L′(s)) ds`, which is (41).

**Formalization Note** `L′` is `deriv (G.L η)`. `L` is smooth on each open unit interval and may have
corners at the integers, a null set for the integrals. The hypothesis on `η` is `0 < η ≤ 1/100`: §5.3's
standing assumption is `W ≥ 1`, `0 < ηW ≤ 10⁻³`, "in particular `η ≤ 1/100`", the lemma does not mention
`W`, and its proof uses only that consequence (through Lemma 5.1). -/
theorem lemma_5_5 {n : ℕ} (hn : 1 ≤ n) (G : Game n) (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 100)
    (T : ℕ) (hT : 1 ≤ T) :
    totalVariation (G.x1 η) (G.l1 η) T ≤
        1 / 4 + Real.exp (3 * η) *
          ∫ s in (1 : ℝ)..(T : ℝ), var (G.x1 η ⌊s⌋₊) (deriv (G.L η) s) ∧
      (∫ s in (1 : ℝ)..(T : ℝ), var (G.x1 η ⌊s⌋₊) (G.L η s)) ≤
        2 * ∑ t ∈ Finset.Icc 1 T, var (G.x1 η t) (G.l1 η t) +
          2 * ∫ s in (1 : ℝ)..(T : ℝ), var (G.x1 η ⌊s⌋₊) (deriv (G.L η) s) := by sorry

end OptHedgeGames
