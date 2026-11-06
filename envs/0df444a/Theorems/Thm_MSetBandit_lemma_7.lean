-- Prove2me | Theorems.Thm_MSetBandit_lemma_7
-- name    : MSetBandit.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:09.941296+00:00
-- url     : https://prove2.me/theorems/2153ab46-1937-487b-8346-3856aecd592f
-- title:
--   Lemma 7 — $G_{\tilde\theta}$ is convex, attains its minimum, its minimizers give the KL projection onto $\mathcal P_\lambda$, and $\zeta(v)$ is a subgradient
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Let $0<\lambda\le1/2$ and $\tilde\theta\in\mathbb R^d$, and let $G_{\tilde\theta}$ be the projection objective (62). Then
--   1. $G_{\tilde\theta}$ is convex on $\mathbb R^d$ and attains its minimum over $\mathbb R^d$;
--   2. for every minimizer $v^\star$,
--   $$
--   p_{\tilde\theta+v^\star}\in\operatorname*{arg\,min}_{p\in\mathcal P_\lambda}\mathrm{KL}(p\,\|\,p_{\tilde\theta}),
--   $$
--   that is, $p_{\tilde\theta+v^\star}\in\mathcal P_\lambda$ and $\mathrm{KL}(p_{\tilde\theta+v^\star}\|p_{\tilde\theta})\le\mathrm{KL}(p\|p_{\tilde\theta})$ for every $p\in\mathcal P_\lambda$;
--   3. for every $v\in\mathbb R^d$, the vector $\zeta(v)$ of (64) is a subgradient of $G_{\tilde\theta}$ at $v$, i.e. $G_{\tilde\theta}(u)\ge G_{\tilde\theta}(v)+\zeta(v)^\top(u-v)$ for every $u\in\mathbb R^d$, and $\|\zeta(v)\|_\infty\le1$.
--
--   The lemma reduces the KL projection onto $\mathcal P_\lambda$ to a $d$-dimensional convex problem that the ellipsoid method can solve without enumerating the actions.
--
--   Differences from the source:
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
--   - encoding: $\mathrm{KL}(p\|q)$ with $+\infty$ when $p(x)>0=q(x)$ → the finite sum $\sum_xp(x)\log(p(x)/q(x))$ (`ConvexRMDP.kl`); reason: every second argument is a weighted $m$-set distribution or $U$, which has full support, so the values agree
--   - encoding: $p_{\tilde\theta+v^\star}\in\arg\min_{p\in\mathcal P_\lambda}\mathrm{KL}(p\|p_{\tilde\theta})$ → membership in $\mathcal P_\lambda$ and $\mathrm{KL}(p_{\tilde\theta+v^\star}\|p_{\tilde\theta})\le\mathrm{KL}(p\|p_{\tilde\theta})$ for every $p\in\mathcal P_\lambda$; reason: definition of the argmin
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix D.1, Lemma 7, p.34

import Mathlib
import Definitions.Def_ConvexRMDP_kl
import Definitions.Def_MSetBandit_Plam
import Definitions.Def_MSetBandit_wdist
import Definitions.Def_MSetBandit_projObj
import Definitions.Def_MSetBandit_subgradZeta
open Matrix

namespace MSetBandit

/-- **Lemma 7** (Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix D.1, p.34). Let `0 < λ ≤ 1/2` and `θ̃ ∈ ℝ^d`. The function `G_θ̃`
of (62) is convex and attains its minimum over `ℝ^d`. For every minimizer `v⋆`,
`p_{θ̃+v⋆} ∈ argmin_{p∈P_λ} KL(p ‖ p_θ̃)` (63). Moreover, for every `v ∈ ℝ^d`, the vector `ζ(v)`
of (64) is a subgradient of `G_θ̃` at `v`, with `‖ζ(v)‖_∞ ≤ 1`.

**Formalization Note.** `1 ≤ m ≤ d − 1` is the paper's standing assumption. Membership in the
argmin is written as `p_{θ̃+v⋆} ∈ P_λ` together with `KL(p_{θ̃+v⋆} ‖ p_θ̃) ≤ KL(p ‖ p_θ̃)` for every
`p ∈ P_λ`. `KL` is the finite-sum divergence `ConvexRMDP.kl` (with `0 log 0 = 0`); its second
argument `p_θ̃` has full support, so it is the paper's divergence. "Subgradient" is the inequality
`G(u) ≥ G(v) + ζ(v)^⊤(u − v)` for every `u` (p.33). -/
theorem lemma_7 {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam ≤ 1 / 2) (θt : Fin d → ℝ) :
    ConvexOn ℝ Set.univ (projObj m lam θt) ∧
    (∃ v : Fin d → ℝ, ∀ u, projObj m lam θt v ≤ projObj m lam θt u) ∧
    (∀ vs : Fin d → ℝ, (∀ u, projObj m lam θt vs ≤ projObj m lam θt u) →
      wdist (m := m) (θt + vs) ∈ Plam lam ∧
      ∀ p ∈ Plam (d := d) (m := m) lam,
        ConvexRMDP.kl (wdist (m := m) (θt + vs)) (wdist θt) ≤ ConvexRMDP.kl p (wdist θt)) ∧
    (∀ v : Fin d → ℝ,
      (∀ u, projObj m lam θt v + subgradZeta m lam θt v ⬝ᵥ (u - v) ≤ projObj m lam θt u) ∧
      ∀ i, |subgradZeta m lam θt v i| ≤ 1) := by sorry

end MSetBandit
