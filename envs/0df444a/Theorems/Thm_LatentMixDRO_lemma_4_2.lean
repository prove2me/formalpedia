-- Prove2me | Theorems.Thm_LatentMixDRO_lemma_4_2
-- name    : LatentMixDRO.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:47.931312+00:00
-- url     : https://prove2.me/theorems/a516d52a-a76e-4603-b923-c8e2a5b52865
-- title:
--   Lemma 4.2 — uniform plug-in bound (corrected: truncation $\epsilon^{q-1}$, constant $B^\circ$)
-- statement:
--   Let Assumptions A1 and A3 hold, $\operatorname{diam}(\mathcal X)+\operatorname{diam}(\mathcal Y)\le R$, $p\in(1,2]$, $q=p/(p-1)$ and $\epsilon>0$. For every sample of size $n\ge1$ in $\mathcal X\times\mathcal Y$, every $\theta\in\Theta$ and every $\eta\in[0,M]$,
--
--   $$
--   \Big|\epsilon^{q-1}\vee\widehat R_{p,\epsilon,L}(\theta,\eta)-\epsilon^{q-1}\vee R_{p,\epsilon,L}(\theta,\eta)\Big|\le B^\circ_\epsilon\,W_{p-1}(\widehat P_n,P),
--   $$
--
--   where $B^\circ_\epsilon=2LR^{2-p}+4\epsilon^{-1}L^pR+\epsilon^{-1}M^{p-1}LR^{2-p}$.
--
--   This reduces the statistical error of the plug-in to a single Wasserstein distance, uniformly over the parameter.
--
--   Differences from the source:
--   - reading: the truncation level $\epsilon\vee$ → $\epsilon^{q-1}\vee$; reason: the proof establishes the $\epsilon^{q-1}\vee$ form (last displays of D.7, p.39) and the proof of Theorem 1 applies the lemma in that form (p.40); the two coincide at $p=2$, where $q-1=1$; no claim is made that the printed $\epsilon\vee$ form is false
--   - correction: the constant $B_\epsilon$ of (17) → $B^\circ_\epsilon=2LR^{2-p}+4\epsilon^{-1}L^pR+\epsilon^{-1}M^{p-1}LR^{2-p}$; reason: with $\epsilon^{q-1}\vee$, (17) is false for $p<2$: $p=3/2$, $L=10^{-5}$, $R=0.01$, $M=LR$, $\epsilon=\sqrt{LR}/2$, $\mathcal X=\{0,R\}$, $\mathcal Y=\{0\}$, $\ell=Lx$, $P(X=R)=1/2$, sample $(0,R,R)$, $\eta=0$ gives left side $1.33\cdot10^{-8}$ against $B_\epsilon W=5.15\cdot10^{-9}$
--   - reading: $\mathcal Y$ unspecified, $\|(x,y)-(x',y')\|$ → $\mathcal Y\subset\mathbb R$ and the Euclidean distance `dist2`; reason: the rate exponent $d+1$ forces this dimension
--   - generalization: the Hölder constant $L^{p-1}$ with $c>0$ in the definition on p.9, so $L>0$ → $L\ge0$; reason: at $L=0$ the losses are constant on $\mathcal X\times\mathcal Y$ and the statement stays true; every $L>0$ is an instance
--   - encoding: $\sup_{\theta,\eta}$ → a bound for each $\theta$ and $\eta\in[0,M]$ on samples in $\mathcal X\times\mathcal Y$; reason: equivalent to the supremum; a sample from $P$ lies there almost surely
--   - encoding: $\operatorname{diam}(\mathcal X)+\operatorname{diam}(\mathcal Y)\le R$ → `Bornology.IsBounded` of $\mathcal X$ and $\mathcal Y$ and `Metric.diam X + Metric.diam Y ≤ R`; reason: `Metric.diam` is $0$ on unbounded sets, and the page's finite diameters already mean bounded sets, so no instance changes
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Lemma 4.2, p.11, and Appendix D.7, pp.37–39

import Mathlib
import Definitions.Def_LatentMixDRO_dist2
import Definitions.Def_LatentMixDRO_IsCondRisk
import Definitions.Def_LatentMixDRO_popR
import Definitions.Def_LatentMixDRO_empR
import Definitions.Def_LatentMixDRO_holderDev
import Definitions.Def_LatentMixDRO_BepsCor

open MeasureTheory

namespace LatentMixDRO

/-- Lemma 4.2 (corrected: truncation `ε^{q-1}`, constant `B°_ε`): the uniform plug-in bound. Under
Assumptions A1 and A3, `diam(𝒳) + diam(𝒴) ≤ R`, `p ∈ (1, 2]`, for every sample in `𝒳 × 𝒴`, every
`θ` and every `η ∈ [0, M]`,
`|ε^{q-1} ∨ R̂_{p,ε,L}(θ, η) - ε^{q-1} ∨ R_{p,ε,L}(θ, η)| ≤ B°_ε W_{p-1}(P̂_n, P)`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, Lemma 4.2, p.11; proof in Appendix D.7, pp.37–39.

**Formalization Note.** The bound is pointwise in `(θ, η)`, which is equivalent to the printed supremum
and avoids a real `⨆`. The truncation level `ε^{q-1}` is the one D.7's last displays bound and the one
p.40 uses; the page prints `ε ∨`. The constant is `BepsCor`: with `ε^{q-1} ∨`, (17) fails for `p < 2`
(`p = 3/2`, `L = 10⁻⁵`, `R = 0.01`, `M = LR`, `ε = √(LR)/2`, `𝒳 = {0, R}`, `𝒴 = {0}`, `ℓ = Lx`,
`P(X = R) = 1/2`, sample `(0, R, R)`, `η = 0`: the left side is `1.33·10⁻⁸`, `B_ε W = 5.15·10⁻⁹`). -/
theorem lemma_4_2 {d n : ℕ} {Θ : Type*} (X : Set (EuclideanSpace ℝ (Fin d))) (Y : Set ℝ)
    (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure P]
    (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (z : Θ → EuclideanSpace ℝ (Fin d) → ℝ)
    (M L R p ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) (hp : 1 < p) (hp2 : p ≤ 2)
    (hXb : Bornology.IsBounded X) (hYb : Bornology.IsBounded Y)
    (hdiam : Metric.diam X + Metric.diam Y ≤ R)
    (hsupp : ∀ᵐ u ∂P, u ∈ X ×ˢ Y)
    (hA1 : ∀ θ, ∀ u ∈ X ×ˢ Y, 0 ≤ ℓ θ u ∧ ℓ θ u ≤ M)
    (hA3 : ∀ θ, ∀ u ∈ X ×ˢ Y, ∀ u' ∈ X ×ˢ Y, |ℓ θ u - ℓ θ u'| ≤ L * dist2 u u')
    (hA3z : ∀ θ, ∀ x ∈ X, ∀ x' ∈ X, |z θ x - z θ x'| ≤ L * ‖x - x'‖)
    (hz : ∀ θ, IsCondRisk P (ℓ θ) (z θ))
    (hn : 1 ≤ n) (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ) (hω : ∀ i, ω i ∈ X ×ˢ Y)
    (θ : Θ) (η : ℝ) (hη : η ∈ Set.Icc 0 M) :
    |max (empR ω ℓ p ε L θ η) (ε ^ (p / (p - 1) - 1))
        - max (popR P X ℓ p ε L θ η) (ε ^ (p / (p - 1) - 1))|
      ≤ BepsCor p ε L R M * holderDev (X ×ˢ Y) (p - 1) ω P := by sorry

end LatentMixDRO
