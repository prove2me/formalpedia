-- Prove2me | Theorems.Thm_HardcoreSlices_proposition_6_3
-- name    : HardcoreSlices.proposition_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:16.161347+00:00
-- url     : https://prove2.me/theorems/73f2c6ac-0c73-4174-b17e-3c7ac142273d
-- title:
--   Proposition 6.3 — $\tilde Z_G(\lambda)$ approximates $Z_G(\lambda)$
-- statement:
--   Let $\gamma$ be a threshold at $\ell=6$, with $\alpha=(1-\gamma)\alpha^*(\Delta)$ and $\beta=4\lambda$. There are $c,C>0$ such that for all large $\Delta$, with high probability over a random $\Delta$-regular bipartite graph $G$, for every $\lambda$ with $\frac1\Delta<\lambda\le\frac c{\sqrt\Delta}$,
--   $$|Z_G(\lambda)-\tilde Z_G(\lambda)|\le\xi\cdot Z_G(\lambda),\qquad\xi=\Bigl(\frac e4\Bigr)^{8\lambda|X|}+e^{-C|X|/\Delta}.$$
--   This reduces counting for the full hardcore model to the slice counters.
--
--   Differences from the source:
--   - reading: λ ≲ 1/√∆ in a section assuming λ > 1/∆ → 1/Δ < λ ≤ c/√Δ; reason: p.26 makes it a standing assumption, and at very small λ the tail exceeds ξ
--   - reading: γ = o∆(1) "fixed globally" (p.19) → every sequence γ with IsThreshold 6 γ; reason: the regimes share one γ (p.4) and p.20 sets ℓ ≥ 6; separate existentials would lose the overlap
--   - generalization: the sentence fixes no order between λ and the high-probability event → λ quantified inside the event, uniformly over its range; reason: the events the proof uses do not mention λ; a fixed-λ statement follows by specialization
--   - reading: the constant C of ξ is not quantified → ∃ C > 0 chosen before ∆ and G; reason: the proof (p.28) says "for some constant C > 0", from Lemma 3.11
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Proposition 6.3, p.27; standing assumption λ > 1/∆, p.26

import Mathlib
import Definitions.Def_HardcoreSlices_IsThreshold
import Definitions.Def_HardcoreSlices_Ztilde

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Proposition 6.3.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.27: "Let `G = (X, Y, E)` be random `∆`-regular bipartite graph with `∆ > 0` sufficiently large and `λ ≲ 1/√∆`. Then with high probability over the
randomness of `G`, `|ZG(λ) − Z̃G(λ)| ≤ ξ · ZG(λ)` for `ξ = (e/4)^{8λ|X|} + e^{−C|X|/∆}`."

**Formalization Note.** `α = (1 − γ)α∗(∆)`, `β = 4λ` (p.26). The range `λ > 1/∆` is the section's standing assumption (p.26, "One additional simplifying assumption we make is `λ > 1/∆`"): at
very small `λ` the tail exceeds `ξ`. `C` is chosen before `∆` and `G`, as "for some constant `C > 0`" on p.28. -/
theorem proposition_6_3 (γ : ℕ → ℝ) (hγ : IsThreshold 6 γ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → AlmostEvery Δ (fun m G =>
      ∀ lam : ℝ, 1 / (Δ : ℝ) < lam → lam ≤ c / Real.sqrt Δ →
        |hardcoreZ G lam - Ztilde G lam ((1 - γ Δ) * alphaStar Δ) (4 * lam)| ≤
          ((Real.exp 1 / 4) ^ (8 * lam * m) + Real.exp (-(C * m / Δ))) * hardcoreZ G lam) := by sorry

end HardcoreSlices
