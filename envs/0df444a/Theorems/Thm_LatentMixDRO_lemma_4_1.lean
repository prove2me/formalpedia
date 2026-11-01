-- Prove2me | Theorems.Thm_LatentMixDRO_lemma_4_1
-- name    : LatentMixDRO.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:37.862262+00:00
-- url     : https://prove2.me/theorems/578d0878-dc00-4fd7-bd86-ecae0bc5aa70
-- title:
--   Lemma 4.1 — the plug-in (14) is the infimum of a convex objective (corrected: coefficient $1/n$)
-- statement:
--   For a sample $(X_1,Y_1),\dots,(X_n,Y_n)$ with $n\ge1$, $p>1$, $L\ge0$, $\epsilon>0$, any $\theta$ and $\eta$,
--
--   $$
--   \widehat R_{p,\epsilon,L}(\theta,\eta)=\inf_{B\in\mathbb R_+^{n\times n}}\widehat R_{p,\epsilon,L}(\theta,\eta,B),
--   $$
--
--   where $\widehat R_{p,\epsilon,L}(\theta,\eta,B)$ is (15) with leading coefficient $1/n$.
--
--   This is what makes the estimator computable: when $\theta\mapsto\ell(\theta;\cdot)$ is convex, the objective is jointly convex in $(\theta,\eta,B)$.
--
--   **Formalization Note** No assumption on the loss values is needed. The result is finite-dimensional convex duality.
--
--   Differences from the source:
--   - correction: the coefficient $(p-1)/n$ in (15) → $1/n$ in (15); reason: the printed lemma is false for $p<2$: at $n=1$, $\ell=1$, $\eta=0$, $p=3/2$, (14) equals $1$ while the printed (15) equals $(1/2)^{2/3}$ for every $B$
--   - generalization: the Hölder constant $L^{p-1}$ with $c>0$ in the definition on p.9, so $L>0$ → $L\ge0$; reason: at $L=0$ the losses are constant on $\mathcal X\times\mathcal Y$ and the statement stays true; every $L>0$ is an instance
--   - generalization: a loss $\ell:\Theta\times(\mathcal X\times\mathcal Y)\to\mathbb R_+$ evaluated at a sample in $\mathcal X\times\mathcal Y$ → any real-valued $\ell$ and any sample points in $\mathbb R^d\times\mathbb R$; reason: the lemma is finite-dimensional convex duality and uses neither the sign of the losses nor where the points lie; the source's case is an instance
--   - encoding: $\inf_{B\ge0}$ → `IsGLB`; reason: Lean convention
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Lemma 4.1, p.10, and Appendix D.6, pp.36–37

import Mathlib
import Definitions.Def_LatentMixDRO_empR
import Definitions.Def_LatentMixDRO_empRB

namespace LatentMixDRO

/-- Lemma 4.1 (corrected: coefficient `1/n` in (15)). For a sample `(X₁, Y₁), …, (X_n, Y_n)`, the
plug-in (14) is the infimum of the convex objective (15):
`R̂_{p,ε,L}(θ, η) = inf_{B ≥ 0} R̂_{p,ε,L}(θ, η, B)` for all `ε > 0`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, Lemma 4.1, p.10; derivation in Appendix D.6, pp.36–37.

**Formalization Note.** `empRB` carries the corrected coefficient `1/n` in place of the printed
`(p - 1)/n`, under which the lemma is false for `p < 2`: at `n = 1`, `ℓ = 1`, `η = 0`, `p = 3/2`,
(14) is `1` and the printed (15) is `(1/2)^{2/3}` for every `B`. Finite-dimensional convex duality:
no boundedness or Lipschitz assumption on the loss values is needed. The infimum is `IsGLB`. -/
theorem lemma_4_1 {d n : ℕ} {Θ : Type*} (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ) (hn : 1 ≤ n)
    (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (θ : Θ) (p ε L η : ℝ) (hp : 1 < p) (hL : 0 ≤ L)
    (hε : 0 < ε) :
    IsGLB {s | ∃ B : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ B i j) ∧ s = empRB ω ℓ p ε L θ η B}
      (empR ω ℓ p ε L θ η) := by sorry

end LatentMixDRO
