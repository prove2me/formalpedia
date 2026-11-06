-- Prove2me | Theorems.Thm_MSetBandit_lemma_8_guarantee
-- name    : MSetBandit.lemma_8_guarantee
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:58.633203+00:00
-- url     : https://prove2.me/theorems/0ecdaea3-180a-48e4-a305-24a9a5f9889a
-- title:
--   Lemma 8 without its complexity count (with (67)) — $v\in\mathcal D_{\mathrm p}$ satisfying (65) exists and gives $p_{\tilde\theta+v}\in\mathcal P_{\lambda/2}$ and (66)
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Let $T\ge1$ be an integer, $0<\eta\le1/(256d)$, and let $\tilde\theta\in\mathbb R^d$ satisfy $\mathrm{KL}(U\|p_{\tilde\theta})\le T$. Let $\lambda=128\eta d$, $\varepsilon_{\mathrm p}=\eta/T$, $B_{\mathrm p}=4dT$, $\mathcal D_{\mathrm p}=\{v\in\mathbb R^d:\|v\|_1\le B_{\mathrm p}\}$ and $\tau=\varepsilon_{\mathrm p}^2/(2B_{\mathrm p}^2)$ as in (60). Then:
--   1. some $v\in\mathcal D_{\mathrm p}$ satisfies (65):
--   $$
--   G_{\tilde\theta}(v)\le\min_{u\in\mathcal D_{\mathrm p}}G_{\tilde\theta}(u)+\tau ;
--   $$
--   2. every global minimizer $v^\star$ of $G_{\tilde\theta}$ over $\mathbb R^d$ satisfies $\|v^\star\|_1\le2dT=B_{\mathrm p}/2$ (67);
--   3. for every $v\in\mathcal D_{\mathrm p}$ satisfying (65), $\theta_+=\tilde\theta+v$ gives a weighted $m$-set distribution $p_{\theta_+}\in\mathcal P_{\lambda/2}$ that satisfies, for every $q\in\mathcal P_\lambda$,
--   $$
--   \mathrm{KL}(q\,\|\,p_{\theta_+})+\mathrm{KL}(p_{\theta_+}\,\|\,p_{\tilde\theta})\le\mathrm{KL}(q\,\|\,p_{\tilde\theta})+\varepsilon_{\mathrm p}. \tag{66}
--   $$
--
--   This is the guarantee of the approximate KL projection used at line 11 of Algorithm 1: an approximate minimizer of $G_{\tilde\theta}$ over the box $\mathcal D_{\mathrm p}$ yields a distribution in $\mathcal P_{\lambda/2}$ with a generalized Pythagorean inequality up to $\varepsilon_{\mathrm p}$.
--
--   Differences from the source:
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
--   - encoding: $\mathrm{KL}(p\|q)$ with $+\infty$ when $p(x)>0=q(x)$ → the finite sum $\sum_xp(x)\log(p(x)/q(x))$ (`ConvexRMDP.kl`); reason: every second argument is a weighted $m$-set distribution or $U$, which has full support, so the values agree
--   - encoding: $\min_{u\in\mathcal D_{\mathrm p}}G_{\tilde\theta}(u)+\tau$ → $G_{\tilde\theta}(u)+\tau$ for every $u$ with $\|u\|_1\le B_{\mathrm p}$; reason: the minimum over the compact set $\mathcal D_{\mathrm p}$ is attained, so the two forms agree
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix D.1, Lemma 8, p.35; the claim "Let v ∈ D_p satisfy (65). We first show …", p.36

import Mathlib
import Definitions.Def_ConvexRMDP_kl
import Definitions.Def_MSetBandit_Plam
import Definitions.Def_MSetBandit_uniform
import Definitions.Def_MSetBandit_wdist
import Definitions.Def_MSetBandit_projObj
open Matrix

namespace MSetBandit

/-- **Lemma 8, the guarantee for an approximate minimizer** (Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix D.1, p.35, with
(67) and the claim of the proof on p.36). Let `T ≥ 1`, `0 < η ≤ 1/(256d)`, and `θ̃ ∈ ℝ^d` satisfy
`KL(U ‖ p_θ̃) ≤ T`. Let `λ = 128ηd`, `ε_p = η/T`, and `B_p = 4dT`, `D_p = {v : ‖v‖₁ ≤ B_p}`,
`τ = ε_p²/(2B_p²)` as in (60). Then:
1. some `v ∈ D_p` satisfies (65), `G_θ̃(v) ≤ min_{u∈D_p} G_θ̃(u) + τ`;
2. every global minimizer `v⋆` of `G_θ̃` satisfies `‖v⋆‖₁ ≤ 2dT = B_p/2` (67);
3. "Let `v ∈ D_p` satisfy (65)": then `θ₊ = θ̃ + v` gives a weighted m-set distribution
   `p_{θ₊} ∈ P_{λ/2}` that satisfies, for every `q ∈ P_λ`,
   `KL(q ‖ p_{θ₊}) + KL(p_{θ₊} ‖ p_θ̃) ≤ KL(q ‖ p_θ̃) + ε_p` (66).

**Formalization Note.** `1 ≤ m ≤ d − 1` is the paper's standing assumption. `min_{u∈D_p}` is
written as "for every `u ∈ D_p`". `KL` is `ConvexRMDP.kl`; every second argument has full support.
Clause 1 is the existence content of "computes a vector `v ∈ D_p` satisfying (65)"; the ellipsoid
method's operation and space counts (the complexity part of Lemma 8) are not part of this
statement. -/
theorem lemma_8_guarantee {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) {T : ℕ} (hT : 1 ≤ T)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / (256 * (d : ℝ))) (θt : Fin d → ℝ)
    (hKL : ConvexRMDP.kl (uniform (d := d) (m := m)) (wdist (m := m) θt) ≤ (T : ℝ)) :
    (∃ v : Fin d → ℝ, ∑ i, |v i| ≤ 4 * (d : ℝ) * T ∧
      ∀ u : Fin d → ℝ, ∑ i, |u i| ≤ 4 * (d : ℝ) * T →
        projObj m (128 * η * d) θt v ≤
          projObj m (128 * η * d) θt u + (η / T) ^ 2 / (2 * (4 * (d : ℝ) * T) ^ 2)) ∧
    (∀ vs : Fin d → ℝ, (∀ u, projObj m (128 * η * d) θt vs ≤ projObj m (128 * η * d) θt u) →
      ∑ i, |vs i| ≤ 2 * (d : ℝ) * T) ∧
    ∀ v : Fin d → ℝ, ∑ i, |v i| ≤ 4 * (d : ℝ) * T →
      (∀ u : Fin d → ℝ, ∑ i, |u i| ≤ 4 * (d : ℝ) * T →
        projObj m (128 * η * d) θt v ≤
          projObj m (128 * η * d) θt u + (η / T) ^ 2 / (2 * (4 * (d : ℝ) * T) ^ 2)) →
      wdist (m := m) (θt + v) ∈ Plam (128 * η * d / 2) ∧
      ∀ q ∈ Plam (d := d) (m := m) (128 * η * d),
        ConvexRMDP.kl q (wdist (θt + v)) + ConvexRMDP.kl (wdist (m := m) (θt + v)) (wdist θt) ≤
          ConvexRMDP.kl q (wdist θt) + η / T := by sorry

end MSetBandit
