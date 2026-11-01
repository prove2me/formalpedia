-- Prove2me | Theorems.Thm_LatentMixDRO_eq_D7_extension
-- name    : LatentMixDRO.eq_D7_extension
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:38.853465+00:00
-- url     : https://prove2.me/theorems/a50d2462-df2d-4b2b-a300-93e7a3cd0abd
-- title:
--   Appendix D.7, first display — Hölder extension
-- statement:
--   Let $(X_1,Y_1),\dots,(X_n,Y_n)$ be a sample with $n\ge1$, $p\in(1,2]$, $L\ge0$, $\epsilon>0$.
--
--   1. Every $h\in\widehat{\mathcal H}_{L,p}$ extends to a $(p-1,L^{p-1})$-Hölder function $\bar h:\mathbb R^d\to\mathbb R$ with $\bar h(X_i)=h(X_i)$ for all $i$ and $\min_i h(X_i)\le\bar h\le\max_i h(X_i)$.
--   2. If every $X_i$ lies in $\mathcal X$, then
--
--   $$
--   \widehat R_{p,\epsilon,L}(\theta,\eta)=\sup_{h\in\mathcal H_{L,p}}\Big\{\mathbb E_{\widehat P_n}\Big[\frac{h(X)}{\epsilon}\big(\ell(\theta;(X,Y))-\eta\big)\Big]\ \Big|\ h\ge0,\ \big(\mathbb E_{\widehat P_n}[h^q(X)]\big)^{1/q}\le\epsilon\Big\}.
--   $$
--
--   So the empirical and population objectives range over the same function class, which makes the two directly comparable.
--
--   Differences from the source:
--   - reading: $\mathrm{range}(\bar h)\subseteq\mathrm{range}(h)$ → values of $\bar h$ between $\min h$ and $\max h$; reason: $\mathrm{range}(h)$ is finite, and a continuous function on $\mathbb R^d$ has connected range; the cited theorem clips to the interval
--   - generalization: the Hölder constant $L^{p-1}$ with $c>0$ in the definition on p.9, so $L>0$ → $L\ge0$; reason: at $L=0$ the losses are constant on $\mathcal X\times\mathcal Y$ and the statement stays true; every $L>0$ is an instance
--   - generalization: a loss $\ell:\Theta\times(\mathcal X\times\mathcal Y)\to\mathbb R_+$ evaluated at a sample in $\mathcal X\times\mathcal Y$ → any real-valued $\ell$, sample covariates in $\mathcal X$ and labels anywhere in $\mathbb R$; reason: the extension argument uses neither the sign of the losses nor the labels; the source's case is an instance
--   - encoding: $\sup$ → `IsLUB`, assuming the sample lies in $\mathcal X$; reason: the empirical law of a sample from $P$ is carried by $\mathcal X$
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Appendix D.7, first display, p.37

import Mathlib
import Definitions.Def_LatentMixDRO_holderClass
import Definitions.Def_LatentMixDRO_empHolderClass
import Definitions.Def_LatentMixDRO_empR

namespace LatentMixDRO

/-- First display of Appendix D.7, with the extension theorem it rests on. (a) Every `h` in the
empirical Hölder class (13) extends to a `(p - 1, L^{p-1})`-Hölder function `h̄` on all of `ℝ^d`
whose values stay between the minimum and the maximum of `h`. (b) Hence `Ĥ_{L,p}` may be replaced by
`H_{L,p}` in (14): `R̂_{p,ε,L}(θ, η) = sup_{h ∈ H_{L,p}} {E_{P̂_n}[(h(X)/ε)(ℓ(θ; (X, Y)) - η)] | h ≥ 0, (E_{P̂_n}[h^q(X)])^{1/q} ≤ ε}`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, Appendix D.7, first display, p.37.

**Formalization Note.** The page writes `range(h̄) ⊆ range(h)`. Since `range(h)` is a finite set and a
continuous function on `ℝ^d` (`d ≥ 1`) has connected range, this is read as: `h̄` takes values
between `min h` and `max h`, stated with witnesses `i, j` so that no real `⨅`/`⨆` enters. Clause (b)
assumes the sample lies in `𝒳`, and the supremum is `IsLUB`. -/
theorem eq_D7_extension {d n : ℕ} {Θ : Type*} (X : Set (EuclideanSpace ℝ (Fin d)))
    (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ) (hn : 1 ≤ n)
    (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (θ : Θ) (p ε L η : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hL : 0 ≤ L) (hε : 0 < ε) :
    (∀ h ∈ empHolderClass ω p L, ∃ hbar : EuclideanSpace ℝ (Fin d) → ℝ,
      hbar ∈ holderClass Set.univ p L ∧ (∀ i, hbar (ω i).1 = h i) ∧
      ∀ x, (∃ i, h i ≤ hbar x) ∧ (∃ j, hbar x ≤ h j)) ∧
    ((∀ i, (ω i).1 ∈ X) →
      IsLUB {s | ∃ h ∈ holderClass X p L, (∀ x ∈ X, 0 ≤ h x) ∧
          ((1 / (n : ℝ)) * ∑ i, h (ω i).1 ^ (p / (p - 1))) ^ (1 / (p / (p - 1))) ≤ ε ∧
          s = (1 / (n : ℝ)) * ∑ i, h (ω i).1 / ε * (ℓ θ (ω i) - η)}
        (empR ω ℓ p ε L θ η)) := by sorry

end LatentMixDRO
