-- Prove2me | Theorems.Thm_NearLinIsing_lemma_3_4
-- name    : NearLinIsing.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:50.665043+00:00
-- url     : https://prove2.me/theorems/b89339dd-4acd-4b93-87a0-df09d2a321fc
-- title:
--   Lemma 3.4 — finite-model log–Sobolev input
-- statement:
--   There is an absolute constant $C_0>0$ such that the following holds. Let $\pi$ be a finite hard-core law on $M$ coordinates with activities at most one. Suppose every feasible occupied marginal after positive pinning is at least $b>0$. Under activities multiplied by $1-t$, assume all such residual laws satisfy
--
--   $$\mathrm{Cov}(X)\preceq C(t)\,\mathrm{Diag}(\mathbb EX),\qquad0\le t<1,$$
--
--   for a nonincreasing $C(t)\ge1$, and put $I=\int_0^1(C(t)-1)/(1-t)\,dt<\infty$. Then for uniform-coordinate heat-bath dynamics $P_{HB}$ and every $f$,
--
--   $$\mathrm{Ent}_\pi(f^2)\le C_0\,Me^I\log\frac Mb\;\mathcal E_{P_{HB}}(f,f).$$
--
--   This is the specialization of [32, Theorem 1.4] that turns a covariance integral and a marginal lower bound into a log–Sobolev inequality.
--
--   Differences from the source:
--   - encoding: O(M e^I log(M/b)) → one absolute constant C₀, quantified before the model; reason: this is the meaning of the O(·) in a lemma about all models
--   - encoding: I < ∞ → integrability of the nonnegative integrand on (0,1); reason: same condition; a non-integrable integrand would otherwise read 0
--   - encoding: activities at most one → 0 < λ_i ≤ 1; reason: activities are positive in the paper (Definition 1.4)
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Lemma 3.4, p. 11

import Mathlib
import Definitions.Def_NearLinIsing_HardCore

open MeasureTheory

namespace NearLinIsing

/-- **Lemma 3.4** (Finite-model log–Sobolev input [32, Theorem 1.4]), p. 11.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Lemma 3.4, p. 11.

There is an absolute constant `C₀ > 0` such that the following holds. Let `π` be a finite
hard-core law on `M` coordinates with activities `0 < λ_i ≤ 1`. Suppose every feasible occupied
marginal after positive pinning is at least `b > 0`. Suppose that, under activities multiplied by
`1 − t`, every residual law after positive pinning satisfies `Cov(X) ⪯ C(t) Diag(EX)` for
`0 ≤ t < 1`, for a nonincreasing `C(t) ≥ 1` with `I = ∫₀¹ (C(t) − 1)/(1 − t) dt < ∞`. Then for the
uniform-coordinate heat-bath dynamics `P_HB` and every `f`,
`Ent_π(f²) ≤ C₀ M e^I log(M/b) E_{P_HB}(f, f)`.

**Formalization Note.** The `O(·)` is one constant `C₀`, quantified before the model. `I < ∞` is
integrability of the nonnegative integrand on `(0, 1)`. A positive pinning is an independent set
`τ`; its residual law is the hard-core law on `resSet Gc τ`. -/
theorem lemma_3_4 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (M : ℕ) (Gc : SimpleGraph (Fin M)) (lam : Fin M → ℝ), (∀ i, 0 < lam i ∧ lam i ≤ 1) →
    ∀ b : ℝ, 0 < b →
    (∀ τ : Finset (Fin M), IsIndep Gc τ → ∀ i ∈ resSet Gc τ,
      b ≤ mean (hcLaw Gc lam (resSet Gc τ)) i) →
    ∀ Cf : ℝ → ℝ, AntitoneOn Cf (Set.Ico 0 1) → (∀ t ∈ Set.Ico (0 : ℝ) 1, 1 ≤ Cf t) →
    (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ τ : Finset (Fin M), IsIndep Gc τ →
      CovLeDiag (hcLaw Gc (fun i => (1 - t) * lam i) (resSet Gc τ))
        (fun i => Cf t * mean (hcLaw Gc (fun i => (1 - t) * lam i) (resSet Gc τ)) i)
        Finset.univ) →
    IntegrableOn (fun t => (Cf t - 1) / (1 - t)) (Set.Ioo 0 1) →
    ∀ f : Finset (Fin M) → ℝ,
      ent (hcLaw Gc lam Finset.univ) (fun X => f X ^ 2) ≤
        C₀ * M * Real.exp (∫ t in (0 : ℝ)..1, (Cf t - 1) / (1 - t)) * Real.log (M / b) *
          hbDirichlet Gc lam f := by sorry

end NearLinIsing
