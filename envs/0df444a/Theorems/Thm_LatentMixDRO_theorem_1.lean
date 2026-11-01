-- Prove2me | Theorems.Thm_LatentMixDRO_theorem_1
-- name    : LatentMixDRO.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:59.976216+00:00
-- url     : https://prove2.me/theorems/42e1db6f-b0b0-4130-94fe-2ad8df5d444c
-- title:
--   Theorem 1 — the marginal DRO estimator nearly minimizes the $L^p$ bound (corrected: coefficient $1/n$ in (15), constants may depend on $R$)
-- statement:
--   Let $\mathcal X\subset\mathbb R^d$ and $\mathcal Y\subset\mathbb R$ be bounded with $\operatorname{diam}(\mathcal X)+\operatorname{diam}(\mathcal Y)\le R$, let $(X,Y)\sim P$ be carried by $\mathcal X\times\mathcal Y$, and let $\alpha_0\in(0,\tfrac12)$, $\epsilon>0$, $p\in(1,2]$, $q=p/(p-1)$, with $(d+1)/2>p-1$. Let the loss take values in $[0,M]$ (Assumption A1), and let it and a version of its conditional risk be $L$-Lipschitz (Assumption A3).
--
--   There are constants $c_1,c_2>0$ depending only on $M,d,p,R$ such that for every $n\ge1$ and $t>0$, with probability at least
--
--   $$
--   1-c_1\exp\big(-c_2\,n\,(t^{\frac{d+1}{p-1}}\wedge t^2)\big),
--   $$
--
--   every empirical minimizer $\hat\theta=\hat\theta^{\mathrm{rob}}_{n,\epsilon}$ of (16), for an i.i.d. sample of size $n$, satisfies
--
--   $$
--   \sup_{Q_0\in\mathcal P_{\alpha_0,X}}\mathbb E_{X\sim Q_0}\big[\mathbb E[\ell(\hat\theta;(X,Y))\mid X]\big]\le\inf_{\eta\in[0,M]}\Big\{\frac1{\alpha_0}\Big(\mathbb E\big[(\mathbb E[\ell(\hat\theta;(X,Y))\mid X]-\eta)_+^{\,p}\big]\Big)^{1/p}+\eta\Big\}
--   $$
--
--   and
--
--   $$
--   \inf_{\eta\in[0,M]}\Big\{\frac1{\alpha_0}\Big(\mathbb E\big[(\mathbb E[\ell(\hat\theta;(X,Y))\mid X]-\eta)_+^{\,p}\big]\Big)^{1/p}+\eta\Big\}\le\inf_{\theta\in\Theta,\eta\in[0,M]}\Big\{\frac1{\alpha_0}\Big(\mathbb E\big[(\mathbb E[\ell(\theta;(X,Y))\mid X]-\eta)_+^{\,p}\big]\Big)^{1/p}+\eta\Big\}+\frac{\epsilon^{q-1}}{\alpha_0}+\frac{2B_\epsilon t}{\alpha_0}.
--   $$
--
--   Here $B_\epsilon$ is the constant (17). The theorem says the estimator's worst-case subpopulation risk is controlled by its $L^p$ bound, and that this bound is nearly the smallest attainable over $\Theta$, at the rate $n^{-(p-1)/(d+1)}$.
--
--   **Formalization Note** The constants are quantified after $d,p,M,R$ and before everything else, so they do not depend on $L,\epsilon,\alpha_0,\Theta,\mathcal X,\mathcal Y,P,\ell,n,t$.
--
--   Differences from the source:
--   - correction: (15) and (16) with coefficient $(p-1)/n$ → coefficient $1/n$; reason: the printed theorem is false for $p<2$: $d=1$, $p=3/2$, $M=L=R=1$, $\alpha_0=1/4$, $\epsilon=0.1$, $\mathcal X=\{0,1\}$, $\mathcal Y=\{0\}$, $P(X=1)=0.2$, $\Theta=\{1,2\}$, $\ell(1;\cdot)\equiv0.93$, $\ell(2;(x,y))=x$: $\hat\theta=2$ with probability tending to $1$ and the second inequality of (18) fails for $t=5\cdot10^{-7}$; also Lemma 4.1 fails at $n=1$
--   - correction: $c_1,c_2$ depending on $M,d,p$ → $c_1,c_2$ depending on $M,d,p,R$, chosen before all other data; reason: the printed form is false: $d=1$, $p=3/2$, $M=1$, $\alpha_0=1/8$, $t=1/256$, and for each $n\ge12$, $\epsilon=1/(3n)$, $R=16\epsilon^{-3}+48\epsilon^{-1}+8\epsilon$, $L=2/R$, $\mathcal X=[0,R/2]$, $\mathcal Y=\{0,R/2\}$, $X$ uniform, $Y$ uniform and independent, $\Theta=\{1,2\}$, $\ell(1;\cdot)\equiv3/4$, $\ell(2;(x,y))=Ly$: the failure probability is at least $1/4$ for all $n\ge12$
--   - reading: $\mathcal Y$ unspecified → $\mathcal Y\subset\mathbb R$ and the Euclidean distance `dist2` on $\mathcal X\times\mathcal Y$; reason: the rate exponent $d+1$ forces this dimension
--   - reading: with probability at least, for $\hat\theta\in\operatorname{argmin}$ → outer measure of the samples at which some minimizer of (16) violates (18) is at most $c_1\exp(\cdots)$; reason: the strongest reading; no measurable selection is needed
--   - generalization: the Hölder constant $L^{p-1}$ with $c>0$ in the definition on p.9, so $L>0$ → $L\ge0$; reason: at $L=0$ the losses are constant on $\mathcal X\times\mathcal Y$ and the statement stays true; every $L>0$ is an instance
--   - encoding: $\sup_{Q_0}$, $\mathbb E[\cdot\mid X]$, unquantified $t$ and $n$ → $\forall Q_0$, the Lipschitz version $z_\theta$ as data, $\forall t>0$, $\forall n\ge1$; reason: Lean conventions; Lemma D.3 says "for any $t>0$"
--   - encoding: $\operatorname{diam}(\mathcal X)+\operatorname{diam}(\mathcal Y)\le R$ → `Bornology.IsBounded` of $\mathcal X$ and $\mathcal Y$ and `Metric.diam X + Metric.diam Y ≤ R`; reason: `Metric.diam` is $0$ on unbounded sets, and the page's finite diameters already mean bounded sets, so no instance changes
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Theorem 1, display (18), p.11

import Mathlib
import Definitions.Def_LatentMixDRO_dist2
import Definitions.Def_LatentMixDRO_IsCondRisk
import Definitions.Def_LatentMixDRO_uncertaintySet
import Definitions.Def_LatentMixDRO_IsEmpMinimizer
import Definitions.Def_LatentMixDRO_Beps
import Definitions.Def_LatentMixDRO_midObj
import Definitions.Def_LatentMixDRO_lowObj

open MeasureTheory

universe u

namespace LatentMixDRO

/-- Theorem 1 (corrected: coefficient `1/n` in (15), constants may depend on `R`), the main result of the
paper. Let Assumptions A1 and A3 hold, `p ∈ (1, 2]`, `diam(𝒳) + diam(𝒴) ≤ R` and `(d + 1)/2 > p - 1`.
For constants `c₁, c₂ > 0` depending on `M, d, p, R`, with probability at least
`1 - c₁ exp(-c₂ n (t^{(d+1)/(p-1)} ∧ t²))`,
`sup_{Q₀ ∈ P_{α₀,X}} E_{X∼Q₀}[E[ℓ(θ̂; (X, Y)) | X]] ≤ inf_{η ∈ [0,M]} {(1/α₀)(E[(E[ℓ(θ̂; (X, Y)) | X] - η)₊^p])^{1/p} + η}
  ≤ inf_{θ ∈ Θ, η ∈ [0,M]} {(1/α₀)(E[(E[ℓ(θ; (X, Y)) | X] - η)₊^p])^{1/p} + η} + ε^{q-1}/α₀ + 2 B_ε t/α₀`,
where `θ̂ = θ̂^rob_{n,ε}` is an empirical minimizer of (16) and `B_ε` is the printed constant (17).

Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures,
arXiv:2007.13982v2, Theorem 1, display (18), p.11.

**Formalization Note.**
* `∃ c₁ c₂` stands after `d, p, M, R` and before `L, ε, α₀, Θ, 𝒳, 𝒴, P, ℓ, z, n, t`: the constants are
  uniform in everything else. With constants independent of `R` the theorem is false (
  `d = 1`, `p = 3/2`, `M = 1`, `α₀ = 1/8`, `t = 1/256`, and for each `n ≥ 12`, `ε = 1/(3n)`,
  `R = 16ε⁻³ + 48ε⁻¹ + 8ε`, `L = 2/R`: failure probability at least `1/4`).
* (15), hence (16), carries the coefficient `1/n` (`empRB`); with the printed `(p - 1)/n` the theorem is
  false for `p < 2`.
* The event is posed on the sample space `(ℝ^d × ℝ)ⁿ` under the product measure. The left side is the
  **outer measure** of the samples at which **some** empirical minimizer violates (18): this is the
  strongest reading of "`θ̂ ∈ argmin`, with probability at least", and needs no measurable selection.
* `𝒴 ⊂ ℝ` with the Euclidean distance `dist2` on `𝒳 × 𝒴`, forced by the exponent `d + 1`.
* The conditional risk is its Lipschitz version `z θ`, taken as data.
* The supremum over `Q₀` is `∀ Q₀`, `midObj` and `lowObj` are the two infima, and `t > 0`, `n ≥ 1` are
  quantified. -/
theorem theorem_1 (d : ℕ) (p M R : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hdim : p - 1 < ((d : ℝ) + 1) / 2) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (L ε α₀ : ℝ), 0 ≤ L → 0 < ε → 0 < α₀ → α₀ < 1 / 2 →
      ∀ {Θ : Type u} (X : Set (EuclideanSpace ℝ (Fin d))) (Y : Set ℝ)
        (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure P]
        (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (z : Θ → EuclideanSpace ℝ (Fin d) → ℝ),
        Bornology.IsBounded X → Bornology.IsBounded Y →
        Metric.diam X + Metric.diam Y ≤ R →
        (∀ᵐ u ∂P, u ∈ X ×ˢ Y) →
        (∀ θ, ∀ u ∈ X ×ˢ Y, 0 ≤ ℓ θ u ∧ ℓ θ u ≤ M) →
        (∀ θ, ∀ u ∈ X ×ˢ Y, ∀ u' ∈ X ×ˢ Y, |ℓ θ u - ℓ θ u'| ≤ L * dist2 u u') →
        (∀ θ, ∀ x ∈ X, ∀ x' ∈ X, |z θ x - z θ x'| ≤ L * ‖x - x'‖) →
        (∀ θ, IsCondRisk P (ℓ θ) (z θ)) →
      ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t →
        Measure.pi (fun _ : Fin n => P)
          {ω | ∃ θhat, IsEmpMinimizer ω ℓ p ε L α₀ M θhat ∧
            ¬ ((∀ Q₀ ∈ uncertaintySet α₀ (P.map Prod.fst),
                  (∫ x, z θhat x ∂Q₀) ≤ midObj P p α₀ M (z θhat)) ∧
                midObj P p α₀ M (z θhat) ≤ lowObj P p α₀ M z + ε ^ (p / (p - 1) - 1) / α₀
                  + 2 * Beps p ε L R M * t / α₀)}
          ≤ ENNReal.ofReal
              (c₁ * Real.exp (-(c₂ * (n : ℝ) * min (t ^ (((d : ℝ) + 1) / (p - 1))) (t ^ 2)))) := by sorry

end LatentMixDRO
