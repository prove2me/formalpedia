-- Prove2me | Theorems.Thm_MonoIncExtrap_lemma_2
-- name    : MonoIncExtrap.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:30:17.432933+00:00
-- url     : https://prove2.me/theorems/ad1abb27-988c-4c74-9664-05b7895362de
-- title:
--   Lemma 2, p.7 — $F_k$ is Lipschitz on $\mathcal Q$ and $\widehat{\mathcal Q}$, uniformly in $k$
-- statement:
--   Assume the standing assumptions of §3: $\varepsilon>0$, $\gamma_0>0$, $z^0\in\mathrm{dom}\,B$, $0<\delta<1$, $0<\nu\le1/2$, $\eta\in[0,\nu/(1+\nu))$, $\rho_0\ge1$, $0<\tau_0\le1$, $\zeta>1$, $0<\sigma<1/\zeta$, Assumption 1 with $\mu=0$, and let $x^*$ be an arbitrary fixed solution of (1). Let $\bar r_0=\|z^0-x^*\|$ and
--   $$
--   \mathcal Q=\Bigl\{x\in\mathrm{dom}\,B:\|x-x^*\|\le\Bigl(\frac{1}{\sqrt{1-2\nu^2}}+1\Bigr)\Bigl(\bar r_0+\frac{\rho_0\tau_0}{1-\sigma\zeta}\Bigr)\Bigr\}.
--   $$
--   Then $F_k$ is $L_{\mathcal Q}$-Lipschitz on $\mathcal Q$ for some $L_{\mathcal Q}>0$ independent of $k$, and $F_k$ is $L_{\widehat{\mathcal Q}}$-Lipschitz, for some $L_{\widehat{\mathcal Q}}>0$ independent of $k$, on
--   $$
--   \widehat{\mathcal Q}=\Bigl\{x\in\mathrm{dom}\,B:\|x-x^*\|\le\Bigl(\frac{5+9\gamma_0L_{\mathcal Q}}{3\sqrt{1-2\nu^2}}+1\Bigr)\Bigl(\bar r_0+\frac{\rho_0\tau_0}{1-\sigma\zeta}\Bigr)\Bigr\}.
--   $$
--
--   These two constants do not depend on $\varepsilon$, which is what makes $\bar M$ an $O(\varepsilon^{-1}\log\varepsilon^{-1})$ bound.
--
--   Differences from the source:
--   - encoding: $F$ is a point-valued operator on $\mathrm{cl}(\mathrm{dom}\,B)$ → a total map on $\mathbb R^n$, constrained only on $\mathrm{cl}(\mathrm{dom}\,B)$; reason: values of $F$ elsewhere never enter $F+B$ or a run, since iterates lie in $\mathrm{dom}\,B$
--   - encoding: Assumption 1(d), the resolvent of $\gamma B$ can be exactly evaluated → a family $J$ with $J_\gamma=(I+\gamma B)^{-1}$ for every $\gamma>0$; reason: the assumption has no mathematical content; the family exists and is unique on $\gamma>0$
--   - generalization: $F_k$ with centre the iterate $z^k$ → $F_k$ with every centre $z\in\mathbb R^n$; reason: the centre does not affect differences of $F_k$; the printed statement is the instance $z=z^k$
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, Lemma 2, p.7

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1
import Definitions.Def_MonoIncExtrap_Algorithm2

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-- **Lemma 2.** arXiv:2206.00973v3, Lemma 2, p.7. There are `L_Q, L_Q̂ > 0`, independent of `k`, such
that `F_k` is `L_Q`-Lipschitz continuous on `Q` of (16) and `L_Q̂`-Lipschitz continuous on `Q̂` of
(17).

**Formalization Note.** The existential comes before `k` and before the centre `zᵏ`, see
`Alg2.ValidQ`. The statement covers `F_k` for every centre, not only the iterates of a run. -/
theorem lemma_2 {n : ℕ}
    {B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))}
    {I : Alg2.Input (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hI : Alg2.Standing B I xstar) :
    ∃ LQ LQhat : ℝ, Alg2.ValidQ B I xstar LQ LQhat := by sorry

end MonoIncExtrap
