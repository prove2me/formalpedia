-- Prove2me | Theorems.Thm_LatentMixDRO_lemma_3_2
-- name    : LatentMixDRO.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:18.190054+00:00
-- url     : https://prove2.me/theorems/221717cc-2cb0-48e6-8690-ff6905613ae4
-- title:
--   Lemma 3.2 — the Hölder-restricted objective approximates the $L^p$ bound
-- statement:
--   Let Assumptions A1 and A3 hold and $p\in(1,2]$, with $q=p/(p-1)$. Fix $\theta\in\Theta$ and $\eta\in\mathbb R$, and write
--
--   $$
--   V=\Big(\mathbb E_{X\sim P_X}\big[(\mathbb E[\ell(\theta;(X,Y))\mid X]-\eta)_+^{\,p}\big]\Big)^{1/p}.
--   $$
--
--   Then:
--
--   1. $V=\inf_{\epsilon>0}\{R_{p,\epsilon,L}(\theta,\eta)\vee\epsilon^{q-1}\}$;
--   2. for every $\epsilon>0$, $\big(R_{p,\epsilon,L}(\theta,\eta)\vee\epsilon^{q-1}\big)-\epsilon^{q-1}\le V$;
--   3. for every $\epsilon>0$, $R_{p,\epsilon,L}(\theta,\eta)\vee\epsilon^{q-1}=V\vee\epsilon^{q-1}$.
--
--   Clause 3 is the identity Appendix D.5 establishes. It implies the two printed claims, and it is the form the proof of Theorem 1 uses.
--
--   **Formalization Note** The conditional risk is the Lipschitz version $z_\theta$ of Assumption A3.
--
--   Differences from the source:
--   - reading: $\inf_{\epsilon\ge0}$ → infimum over $\epsilon>0$ (`IsGLB` on `Set.Ioi 0`); reason: (12) divides by $\epsilon$, so $\epsilon=0$ is undefined
--   - generalization: the two printed claims → those claims plus clause 3, the identity $R\vee\epsilon^{q-1}=V\vee\epsilon^{q-1}$; reason: clause 3 implies the printed claims and is what D.5 proves; clauses 1 and 2 are the source's statement
--   - generalization: the Hölder constant $L^{p-1}$ with $c>0$ in the definition on p.9, so $L>0$ → $L\ge0$; reason: at $L=0$ the losses are constant on $\mathcal X\times\mathcal Y$ and the statement stays true; every $L>0$ is an instance
--   - encoding: $\mathbb E[\ell\mid X]$ with an $L$-Lipschitz version → data $z_\theta$ with `IsCondRisk`; reason: reading R6 of the conditional risk; nothing depends on the version
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Lemma 3.2, p.10, and Appendix D.5, pp.35–36

import Mathlib
import Definitions.Def_LatentMixDRO_dist2
import Definitions.Def_LatentMixDRO_IsCondRisk
import Definitions.Def_LatentMixDRO_lpRisk
import Definitions.Def_LatentMixDRO_popR

open MeasureTheory

namespace LatentMixDRO

/-- Lemma 3.2, with the identity its proof establishes. Under Assumptions A1 and A3 and `p ∈ (1, 2]`,
for every `θ` and `η`, writing `V = (E_{X∼P_X}[(E[ℓ(θ; (X, Y)) | X] - η)₊^p])^{1/p}`:
(a) `V = inf_{ε > 0} {R_{p,ε,L}(θ, η) ∨ ε^{q-1}}`;
(b) for every `ε > 0`, `(R_{p,ε,L}(θ, η) ∨ ε^{q-1}) - ε^{q-1} ≤ V`;
(c) for every `ε > 0`, `R_{p,ε,L}(θ, η) ∨ ε^{q-1} = V ∨ ε^{q-1}`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, Lemma 3.2, p.10; clause (c) is the content of
Appendix D.5, pp.35–36.

**Formalization Note.** The page writes `inf_{ε ≥ 0}`, but (12) divides by `ε`, so the infimum is taken
over `ε > 0`, as `IsGLB`. `q = p/(p - 1)`. `z θ` is the Lipschitz version of the conditional risk that
Assumption A3 provides. Clause (c) implies (a) and (b) and is what the proof of Theorem 1 uses. -/
theorem lemma_3_2 {d : ℕ} {Θ : Type*} (X : Set (EuclideanSpace ℝ (Fin d))) (Y : Set ℝ)
    (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure P]
    (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (z : Θ → EuclideanSpace ℝ (Fin d) → ℝ)
    (M L p : ℝ) (hL : 0 ≤ L) (hp : 1 < p) (hp2 : p ≤ 2)
    (hsupp : ∀ᵐ u ∂P, u ∈ X ×ˢ Y)
    (hA1 : ∀ θ, ∀ u ∈ X ×ˢ Y, 0 ≤ ℓ θ u ∧ ℓ θ u ≤ M)
    (hA3 : ∀ θ, ∀ u ∈ X ×ˢ Y, ∀ u' ∈ X ×ˢ Y, |ℓ θ u - ℓ θ u'| ≤ L * dist2 u u')
    (hA3z : ∀ θ, ∀ x ∈ X, ∀ x' ∈ X, |z θ x - z θ x'| ≤ L * ‖x - x'‖)
    (hz : ∀ θ, IsCondRisk P (ℓ θ) (z θ))
    (θ : Θ) (η : ℝ) :
    IsGLB ((fun ε : ℝ => max (popR P X ℓ p ε L θ η) (ε ^ (p / (p - 1) - 1))) '' Set.Ioi 0)
      (lpRisk P p (z θ) η) ∧
    (∀ ε : ℝ, 0 < ε →
      max (popR P X ℓ p ε L θ η) (ε ^ (p / (p - 1) - 1)) - ε ^ (p / (p - 1) - 1)
        ≤ lpRisk P p (z θ) η) ∧
    (∀ ε : ℝ, 0 < ε →
      max (popR P X ℓ p ε L θ η) (ε ^ (p / (p - 1) - 1))
        = max (lpRisk P p (z θ) η) (ε ^ (p / (p - 1) - 1))) := by sorry

end LatentMixDRO
