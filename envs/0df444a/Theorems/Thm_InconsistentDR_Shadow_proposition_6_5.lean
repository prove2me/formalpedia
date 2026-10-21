-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_proposition_6_5
-- name    : InconsistentDR.Shadow.proposition_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:48.382696+00:00
-- url     : https://prove2.me/theorems/c83b4f7d-cd79-4cd1-88c6-e9e2dd272087
-- title:
--   Proposition 6.5, pp. 24–25 — the primal shadows are bounded, their weak cluster points minimize, and f, g and f + g converge in value
-- statement:
--   Throughout, $X$ is a real Hilbert space, $f, g \in \Gamma_0(X)$ (proper, convex, lower semicontinuous, with values in $]-\infty,+\infty]$), $(A,B) = (\partial f, \partial g)$, $P_f = (\mathrm{Id}+\partial f)^{-1}$ and $P_g$ are the proximal mappings, $R_f = 2P_f - \mathrm{Id}$, $P_{f^*} = \mathrm{Id} - P_f$, and
--   $$T = \mathrm{Id} - P_f + P_g R_f$$
--   is the Douglas–Rachford operator (69). The vector $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$ is the minimal displacement vector of $T$, the standing assumption (12) $\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}$ holds, and $v_R = P_{\overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}}(0) = 0$ (68). In addition $Z \neq \varnothing$ (74).
--
--   Set $\mu = \min_{x\in X}\big(f(x) + g(x - v)\big)$, let $x \in X$, and write $p_n = P_f T^n x$ and $q_n = P_g R_f T^n x$. Then
--   1. $(p_n)_{n\in\mathbb N}$ is bounded and its weak cluster points are minimizers of $f + g(\cdot - v)$;
--   2. $(q_n)_{n\in\mathbb N}$ is bounded and its weak cluster points are minimizers of $f(\cdot + v) + g$.
--
--   Moreover, if $\bar z$ is a weak cluster point of $(p_n)_{n\in\mathbb N}$, then
--   3. $f(p_n) \to f(\bar z)$;
--   4. $g(q_n) \to g(\bar z - v)$;
--   5. $$f(p_n) + g(q_n) \to \mu .$$
--
--   **Formalization Note** $f, g$ are `X → EReal` functions satisfying the published `GammaZero` (never $-\infty$, not identically $+\infty$, convex epigraph, lower semicontinuous); `subgrad f x` is $\partial f(x)$ (empty where $f(x) = +\infty$). The proximal maps are `Pf Pg : X → X` characterized by `IsResolvent 1 (subgrad f) Pf` ($x - P_f x \in \partial f(P_f x)$), which is $P_f = (\mathrm{Id}+\partial f)^{-1}$; $P_{f^*}$ is `resInv Pf` $= \mathrm{Id} - P_f$ (Moreau's decomposition, (8)), and $R_f$ is `refl Pf`. $v$ is the least-norm point of $\overline{\operatorname{ran}}(\mathrm{Id}-T)$. The standing assumptions of §6 (p. 22) are explicit hypotheses: (12) of p. 6, and $v_R = 0$, encoded equivalently as $0 \in \overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}$ (for a closed convex set $C$, $P_C(0) = 0 \iff 0 \in C$). By (68) $v = v_D$, so $v_D$ is not a separate variable. `CompleteSpace X` makes the space Hilbert. The additional standing assumption (74) of p. 24, $Z \neq \varnothing$, is the hypothesis `hZ`, with $Z$ = `solZ (subgrad f) (subgrad g) v` $= \{x \mid 0 \in -v + \partial f(x) + \partial g(x - v)\}$ (14). $\mu$ is the infimum $\inf_y (f(y) + g(y - v))$ in `EReal` (its attainment is part of the statement via items 1 and 5). Weak cluster points are the published `IsWeakClusterPt` (limits of weakly convergent subsequences); boundedness is `Bornology.IsBounded` of the range.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), pp. 24–25, Proposition 6.5

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

/-- Proposition 6.5, pp. 24–25, under the standing assumptions of §6 and (74). With
`µ := min (f + g(· − v))`, `pₙ = P_f Tⁿx`, `qₙ = P_g R_f Tⁿx`:
(i) `(pₙ)` is bounded and its weak cluster points minimize `f + g(· − v)`;
(ii) `(qₙ)` is bounded and its weak cluster points minimize `f(· + v) + g`;
and for every weak cluster point `z̄` of `(pₙ)`: (iii) `f(pₙ) → f(z̄)`, (iv) `g(qₙ) → g(z̄ − v)`,
(v) `f(pₙ) + g(qₙ) → µ`. -/
theorem proposition_6_5 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)))
    (hZ : (solZ (subgrad f) (subgrad g) v).Nonempty)
    (x : X) :
    let μ : EReal := ⨅ y, f y + g (y - v)
    let p : ℕ → X := fun n => Pf ((drT Pf Pg)^[n] x)
    let q : ℕ → X := fun n => Pg (refl Pf ((drT Pf Pg)^[n] x))
    (Bornology.IsBounded (Set.range p) ∧
      ∀ z, IsWeakClusterPt p z → ∀ y, f z + g (z - v) ≤ f y + g (y - v)) ∧
    (Bornology.IsBounded (Set.range q) ∧
      ∀ w, IsWeakClusterPt q w → ∀ y, f (w + v) + g w ≤ f (y + v) + g y) ∧
    (∀ z, IsWeakClusterPt p z →
      Tendsto (fun n => f (p n)) atTop (𝓝 (f z)) ∧
      Tendsto (fun n => g (q n)) atTop (𝓝 (g (z - v))) ∧
      Tendsto (fun n => f (p n) + g (q n)) atTop (𝓝 μ)) := by sorry

end InconsistentDR.Shadow
