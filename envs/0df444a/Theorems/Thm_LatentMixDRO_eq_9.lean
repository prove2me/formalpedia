-- Prove2me | Theorems.Thm_LatentMixDRO_eq_9
-- name    : LatentMixDRO.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:54.748291+00:00
-- url     : https://prove2.me/theorems/38200cd8-0fed-4f3a-a7aa-5d5fd2a7833f
-- title:
--   Display (9) — the $L^p$ bound and its variational form
-- statement:
--   Let $P$ be a law of $(X,Y)$ carried by $\mathcal X\times\mathcal Y$, $f$ an integrable function on $\mathbb R^d\times\mathbb R$ (the loss $\ell(\theta;\cdot)$), and $z$ a version of $\mathbb E[f\mid X]$. For $p\in(1,\infty)$, $q=p/(p-1)$ and $\eta\in\mathbb R$,
--
--   $$
--   \mathbb E_{X\sim P_X}\big[(z(X)-\eta)_+\big]\le\Big(\mathbb E_{X\sim P_X}\big[(z(X)-\eta)_+^{\,p}\big]\Big)^{1/p}=\sup_h\big\{\mathbb E[h(X)(f(X,Y)-\eta)]\ \big|\ h:\mathcal X\to\mathbb R_+,\ \mathbb E[h(X)^q]\le1\big\}.
--   $$
--
--   The inequality gives the $L^p$ upper bound on the CVaR objective. The equality expresses that bound through the loss itself, without the conditional expectation.
--
--   **Formalization Note** The constraint $\mathbb E[h(X)^q]\le1$ is `eLpNorm` at most $1$. No boundedness of the loss is assumed, as on the page. When $(z-\eta)_+^p$ is integrable, the inequality holds and the right side is the least upper bound (`IsLUB`) of the values; otherwise both sides of the equality are $+\infty$, stated as: the set of values is not bounded above.
--
--   Differences from the source:
--   - encoding: the equality of extended reals → two cases: if $(z-\eta)_+^p$ is integrable, the inequality and `IsLUB` of the real $L^p$ norm; if not, the set of values is unbounded above; reason: Lean's real Bochner integral is $0$ on non-integrable functions, so the $+\infty$ case is stated separately
--   - encoding: $h:\mathcal X\to\mathbb R_+$ with $\mathbb E[h(X)^q]$ meaningful → $h$ a.e.-strongly measurable, $h\ge0$ on $\mathcal X$, `eLpNorm` constraint; reason: the expectation in the source presupposes measurability; $\mathcal X$ carries $P_X$
--   - encoding: $\mathbb E[\ell\mid X]$ → a version $z$ of the conditional expectation of an integrable $f$ (hypothesis `Integrable f P`); reason: the source presupposes integrability; Mathlib's `condExp` is $0$ otherwise
--   - encoding: $\sup$ → `IsLUB`; reason: Lean convention
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (9), p.9

import Mathlib
import Definitions.Def_LatentMixDRO_IsCondRisk
import Definitions.Def_LatentMixDRO_lpRisk

open MeasureTheory

namespace LatentMixDRO

/-- Display (9): for `p ∈ (1, ∞)` and `q = p/(p - 1)`,
`E[(z(X) - η)₊] ≤ (E[(z(X) - η)₊^p])^{1/p} = sup_h {E[h(X)(f(X, Y) - η)] | h : 𝒳 → ℝ₊, E[h(X)^q] ≤ 1}`,
where `f = ℓ(θ; ·)` and `z = E[f | X]`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (9), p.9.

**Formalization Note.** Stated for one loss `f = ℓ(θ; ·)`, any `η ∈ ℝ`, with no boundedness of the
loss (the page assumes none for (9)). `Integrable f P` makes `E[f | X]` meaningful (Mathlib's `condExp`
is `0` otherwise). The test functions are a.e.-strongly measurable, as `E[h(X)^q]` requires, and the
constraint uses `eLpNorm`. When `(z - η)₊^p` is integrable the `L^p` norm is finite: the first
inequality holds and the supremum is `IsLUB`. Otherwise both sides of the equality are `+∞`: the set
of values is unbounded above (and the first inequality is trivial). -/
theorem eq_9 {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure P]
    (X : Set (EuclideanSpace ℝ (Fin d))) (Y : Set ℝ) (hsupp : ∀ᵐ u ∂P, u ∈ X ×ˢ Y)
    (f : EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (z : EuclideanSpace ℝ (Fin d) → ℝ) (p η : ℝ)
    (hf : Integrable f P) (hz : IsCondRisk P f z) (hp : 1 < p) :
    (Integrable (fun x => (max (z x - η) 0) ^ p) (P.map Prod.fst) →
      (∫ x, max (z x - η) 0 ∂(P.map Prod.fst)) ≤ lpRisk P p z η ∧
      IsLUB {s | ∃ h : EuclideanSpace ℝ (Fin d) → ℝ,
          AEStronglyMeasurable h (P.map Prod.fst) ∧ (∀ x ∈ X, 0 ≤ h x) ∧
          eLpNorm h (ENNReal.ofReal (p / (p - 1))) (P.map Prod.fst) ≤ 1 ∧
          s = ∫ u, h u.1 * (f u - η) ∂P}
        (lpRisk P p z η)) ∧
    (¬ Integrable (fun x => (max (z x - η) 0) ^ p) (P.map Prod.fst) →
      ¬ BddAbove {s | ∃ h : EuclideanSpace ℝ (Fin d) → ℝ,
          AEStronglyMeasurable h (P.map Prod.fst) ∧ (∀ x ∈ X, 0 ≤ h x) ∧
          eLpNorm h (ENNReal.ofReal (p / (p - 1))) (P.map Prod.fst) ≤ 1 ∧
          s = ∫ u, h u.1 * (f u - η) ∂P}) := by sorry

end LatentMixDRO
