-- Prove2me | Theorems.Thm_LatentMixDRO_proof_thm1_chain
-- name    : LatentMixDRO.proof_thm1_chain
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:59.11384+00:00
-- url     : https://prove2.me/theorems/b9d5934b-501d-4edf-95d7-b42eea89da4e
-- title:
--   Appendix D.8 — the deterministic chain behind (18) (corrected: constant $B^\circ$)
-- statement:
--   Under the assumptions of Theorem 1, take any sample of size $n\ge1$ in $\mathcal X\times\mathcal Y$ and any empirical minimizer $\hat\theta$ of (16). With $W=W_{p-1}(\widehat P_n,P)$,
--
--   $$
--   \sup_{Q_0\in\mathcal P_{\alpha_0,X}}\mathbb E_{X\sim Q_0}\big[\mathbb E[\ell(\hat\theta;(X,Y))\mid X]\big]\le\inf_{\eta\in[0,M]}\Big\{\frac1{\alpha_0}\Big(\mathbb E\big[(\mathbb E[\ell(\hat\theta;(X,Y))\mid X]-\eta)_+^{\,p}\big]\Big)^{1/p}+\eta\Big\}
--   $$
--
--   and the right side is at most
--
--   $$
--   \inf_{\theta\in\Theta,\eta\in[0,M]}\Big\{\frac1{\alpha_0}\Big(\mathbb E\big[(\mathbb E[\ell(\theta;(X,Y))\mid X]-\eta)_+^{\,p}\big]\Big)^{1/p}+\eta\Big\}+\frac{\epsilon^{q-1}}{\alpha_0}+\frac{2B^\circ_\epsilon W}{\alpha_0}.
--   $$
--
--   This is the optimization half of the main theorem; the probabilistic half is the concentration of $W$.
--
--   Differences from the source:
--   - encoding: with probability at least $1-\gamma$, with $t$ → for every sample in $\mathcal X\times\mathcal Y$, with $W$ in place of $t$; reason: the probability enters only through the event $\{W<t\}$
--   - correction: $B_\epsilon$ of (17) → $B^\circ_\epsilon$; reason: (17) is false in Lemma 4.2 for $p<2$; same counterexample as Lemma 4.2
--   - reading: the printed $\vee\epsilon$ in the fourth line → $\vee\epsilon^{q-1}$; reason: the next line prints $\epsilon^{q-1}$ and every other line has $\vee\epsilon^{q-1}$; at $q=2$ they agree
--   - generalization: the Hölder constant $L^{p-1}$ with $c>0$ in the definition on p.9, so $L>0$ → $L\ge0$; reason: at $L=0$ the losses are constant on $\mathcal X\times\mathcal Y$ and the statement stays true; every $L>0$ is an instance
--   - encoding: $\sup_{Q_0}$ → $\forall Q_0$; reason: Lean convention; avoids a real supremum over measures
--   - encoding: $\operatorname{diam}(\mathcal X)+\operatorname{diam}(\mathcal Y)\le R$ → `Bornology.IsBounded` of $\mathcal X$ and $\mathcal Y$ and `Metric.diam X + Metric.diam Y ≤ R`; reason: `Metric.diam` is $0$ on unbounded sets, and the page's finite diameters already mean bounded sets, so no instance changes
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Appendix D.8, p.40

import Mathlib
import Definitions.Def_LatentMixDRO_dist2
import Definitions.Def_LatentMixDRO_IsCondRisk
import Definitions.Def_LatentMixDRO_uncertaintySet
import Definitions.Def_LatentMixDRO_IsEmpMinimizer
import Definitions.Def_LatentMixDRO_holderDev
import Definitions.Def_LatentMixDRO_BepsCor
import Definitions.Def_LatentMixDRO_midObj
import Definitions.Def_LatentMixDRO_lowObj

open MeasureTheory

namespace LatentMixDRO

/-- The chain of Appendix D.8, deterministic form: for every sample in `𝒳 × 𝒴` and every empirical
minimizer `θ̂` of (16), with `W = W_{p-1}(P̂_n, P)`,
`sup_{Q₀ ∈ P_{α₀,X}} E_{X∼Q₀}[E[ℓ(θ̂; (X, Y)) | X]] ≤ inf_{η ∈ [0,M]} {(1/α₀)(E[(E[ℓ(θ̂; (X, Y)) | X] - η)₊^p])^{1/p} + η}
  ≤ inf_{θ ∈ Θ, η ∈ [0,M]} {(1/α₀)(E[(E[ℓ(θ; (X, Y)) | X] - η)₊^p])^{1/p} + η} + ε^{q-1}/α₀ + 2 B°_ε W/α₀`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, Appendix D.8, p.40.

**Formalization Note.** The page's "with probability at least `1 - γ`" disappears by keeping `W` in place
of `t`. The constant is `BepsCor` (see `lemma_4_2`). The page's fourth line prints `∨ ε`; it is read as
`∨ ε^{q-1}`, as in every other line of the chain. The supremum over `Q₀` is `∀ Q₀`. -/
theorem proof_thm1_chain {d n : ℕ} {Θ : Type*} (X : Set (EuclideanSpace ℝ (Fin d))) (Y : Set ℝ)
    (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure P]
    (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (z : Θ → EuclideanSpace ℝ (Fin d) → ℝ)
    (M L R p ε α₀ : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) (hα₀ : 0 < α₀) (hα₀' : α₀ < 1 / 2)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hXb : Bornology.IsBounded X) (hYb : Bornology.IsBounded Y)
    (hdiam : Metric.diam X + Metric.diam Y ≤ R)
    (hsupp : ∀ᵐ u ∂P, u ∈ X ×ˢ Y)
    (hA1 : ∀ θ, ∀ u ∈ X ×ˢ Y, 0 ≤ ℓ θ u ∧ ℓ θ u ≤ M)
    (hA3 : ∀ θ, ∀ u ∈ X ×ˢ Y, ∀ u' ∈ X ×ˢ Y, |ℓ θ u - ℓ θ u'| ≤ L * dist2 u u')
    (hA3z : ∀ θ, ∀ x ∈ X, ∀ x' ∈ X, |z θ x - z θ x'| ≤ L * ‖x - x'‖)
    (hz : ∀ θ, IsCondRisk P (ℓ θ) (z θ))
    (hn : 1 ≤ n) (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ) (hω : ∀ i, ω i ∈ X ×ˢ Y)
    (θhat : Θ) (hθhat : IsEmpMinimizer ω ℓ p ε L α₀ M θhat) :
    (∀ Q₀ ∈ uncertaintySet α₀ (P.map Prod.fst), (∫ x, z θhat x ∂Q₀) ≤ midObj P p α₀ M (z θhat)) ∧
    midObj P p α₀ M (z θhat) ≤ lowObj P p α₀ M z + ε ^ (p / (p - 1) - 1) / α₀
      + 2 * BepsCor p ε L R M * holderDev (X ×ˢ Y) (p - 1) ω P / α₀ := by sorry

end LatentMixDRO
