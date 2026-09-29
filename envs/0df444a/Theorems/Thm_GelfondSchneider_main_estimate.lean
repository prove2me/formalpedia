-- Prove2me | Theorems.Thm_GelfondSchneider_main_estimate
-- name    : GelfondSchneider.main_estimate
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:05:29.3611+00:00
-- url     : https://prove2.me/theorems/afd443ea-1ee0-45e7-bf29-99baf10f15ef
-- title:
--   Gelfond's main estimate: r^{(r-3h)/2} ≤ C^r for arbitrarily large r
-- statement:
--   Let $K$ be a number field of degree $h$ with an embedding $\sigma$, and $\alpha', \beta', \gamma' \in K$ with $\sigma(\alpha') = e^{l}$, $\sigma(\beta') = \beta$ and $\sigma(\gamma') = e^{\beta l}$, where $l \ne 0$ and $\beta$ is irrational. Then there is $C \ge 1$ such that for every $N$ there is $r \ge N$ with
--
--   $$r^{(r - 3h)/2} \le C^{r}.$$
--
--   This is where Gelfond's argument ends: with $m = 2h + 2$, the auxiliary function of `GelfondSchneider.aux_coeffs` has a first non-zero derivative whose value is an algebraic number bounded below by `Transcendence.liouville_house` and above by `GelfondSchneider.deriv_upper` and `GelfondSchneider.rho_house_le`. The inequality fails for large $r$, which proves the Gelfond–Schneider theorem.
-- source:
--   Known: A. O. Gelfond (1934), T. Schneider (1934); this step of Gelfond's proof. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi), restructuring the formalization by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace GelfondSchneider

theorem main_estimate (K : Type*) [Field K] [NumberField K] (σ : K →+* ℂ) (α' β' γ' : K)
    (l β : ℂ) (hl : l ≠ 0) (hβq : ∀ x : ℚ, β ≠ x)
    (hα : σ α' = Complex.exp l) (hβ : σ β' = β) (hγ : σ γ' = Complex.exp (β * l)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ 0 < r ∧
      (r : ℝ) ^ (((r : ℝ) - 3 * Module.finrank ℚ K) / 2) ≤ C ^ r := by
  sorry

end GelfondSchneider
