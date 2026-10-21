-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_lemma_6_3
-- name    : InconsistentDR.Shadow.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:29.688254+00:00
-- url     : https://prove2.me/theorems/08044181-3eee-4c86-9302-f6eb0e558ffc
-- title:
--   Lemma 6.3 (the prox lemma), p. 23 — inequalities (71a)–(71c) for P_f x and P_g R_f x against y ∈ dom f ∩ (v + dom g)
-- statement:
--   Throughout, $X$ is a real Hilbert space, $f, g \in \Gamma_0(X)$ (proper, convex, lower semicontinuous, with values in $]-\infty,+\infty]$), $(A,B) = (\partial f, \partial g)$, $P_f = (\mathrm{Id}+\partial f)^{-1}$ and $P_g$ are the proximal mappings, $R_f = 2P_f - \mathrm{Id}$, $P_{f^*} = \mathrm{Id} - P_f$, and
--   $$T = \mathrm{Id} - P_f + P_g R_f$$
--   is the Douglas–Rachford operator (69). The vector $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$ is the minimal displacement vector of $T$, the standing assumption (12) $\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}$ holds, and $v_R = P_{\overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}}(0) = 0$ (68).
--
--   Let $x \in X$ and $y \in \operatorname{dom}f \cap (v + \operatorname{dom}g)$. Then
--   $$0 \ge \langle y - P_f x, v\rangle, \tag{71a}$$
--   $$f(y) \ge f(P_f x) + \langle y - P_f x, v + P_{f^*}x\rangle, \tag{71b}$$
--   $$g(y - v) \ge g(P_g R_f x) + \langle y - P_g R_f x - v, P_f x - P_g R_f x - v\rangle + \langle -y + v + P_g R_f x, v + P_{f^*}x\rangle. \tag{71c}$$
--
--   Summed along the orbit $x = T^n x_0$, these inequalities give the descent estimate (78) of Proposition 6.4.
--
--   **Formalization Note** $f, g$ are `X → EReal` functions satisfying the published `GammaZero` (never $-\infty$, not identically $+\infty$, convex epigraph, lower semicontinuous); `subgrad f x` is $\partial f(x)$ (empty where $f(x) = +\infty$). The proximal maps are `Pf Pg : X → X` characterized by `IsResolvent 1 (subgrad f) Pf` ($x - P_f x \in \partial f(P_f x)$), which is $P_f = (\mathrm{Id}+\partial f)^{-1}$; $P_{f^*}$ is `resInv Pf` $= \mathrm{Id} - P_f$ (Moreau's decomposition, (8)), and $R_f$ is `refl Pf`. $v$ is the least-norm point of $\overline{\operatorname{ran}}(\mathrm{Id}-T)$. The standing assumptions of §6 (p. 22) are explicit hypotheses: (12) of p. 6, and $v_R = 0$, encoded equivalently as $0 \in \overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}$ (for a closed convex set $C$, $P_C(0) = 0 \iff 0 \in C$). By (68) $v = v_D$, so $v_D$ is not a separate variable. `CompleteSpace X` makes the space Hilbert. The condition $y \in v + \operatorname{dom} g$ is written $y - v \in \operatorname{dom} g$, and each inequality is stated as `EReal value + (real : EReal) ≤ EReal value`, so no extended-real subtraction occurs.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 23, Lemma 6.3, (71a)–(71c)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

/-- Lemma 6.3 (the prox lemma), p. 23, under the standing assumptions of §6. For `x ∈ X` and
`y ∈ dom f ∩ (v + dom g)`, with `P_{f*} = resInv Pf` (by (8)) and `R_f = refl Pf`:
(71a) `0 ≥ ⟨y − P_f x, v⟩`; (71b) `f(y) ≥ f(P_f x) + ⟨y − P_f x, v + P_{f*} x⟩`;
(71c) `g(y − v) ≥ g(P_g R_f x) + ⟨y − P_g R_f x − v, P_f x − P_g R_f x − v⟩
+ ⟨−y + v + P_g R_f x, v + P_{f*} x⟩`. -/
theorem lemma_6_3 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)))
    (x y : X) (hy : y ∈ edom f ∧ y - v ∈ edom g) :
    ⟪y - Pf x, v⟫_ℝ ≤ 0 ∧
    f (Pf x) + ((⟪y - Pf x, v + resInv Pf x⟫_ℝ : ℝ) : EReal) ≤ f y ∧
    g (Pg (refl Pf x)) +
        ((⟪y - Pg (refl Pf x) - v, Pf x - Pg (refl Pf x) - v⟫_ℝ +
          ⟪-y + v + Pg (refl Pf x), v + resInv Pf x⟫_ℝ : ℝ) : EReal) ≤ g (y - v) := by sorry

end InconsistentDR.Shadow
