-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_proposition_6_2
-- name    : InconsistentDR.Shadow.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:27.549821+00:00
-- url     : https://prove2.me/theorems/3e7d9dab-378c-4603-900b-67b8f2d94c14
-- title:
--   Proposition 6.2, p. 23 — Z = {x | 0 ∈ ∂f(x) + ∂g(x − v)}, and Z ≠ ∅ ⇒ Z = argmin(f + g(· − v))
-- statement:
--   Throughout, $X$ is a real Hilbert space, $f, g \in \Gamma_0(X)$ (proper, convex, lower semicontinuous, with values in $]-\infty,+\infty]$), $(A,B) = (\partial f, \partial g)$, $P_f = (\mathrm{Id}+\partial f)^{-1}$ and $P_g$ are the proximal mappings, $R_f = 2P_f - \mathrm{Id}$, $P_{f^*} = \mathrm{Id} - P_f$, and
--   $$T = \mathrm{Id} - P_f + P_g R_f$$
--   is the Douglas–Rachford operator (69). The vector $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$ is the minimal displacement vector of $T$, the standing assumption (12) $\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}$ holds, and $v_R = P_{\overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}}(0) = 0$ (68).
--
--   Let $Z = \{x \mid 0 \in -v + \partial f(x) + \partial g(x - v)\}$ (14). Then
--   1. $Z = \{x \in X \mid 0 \in \partial f(x) + \partial g(x - v)\}$;
--   2. if $Z \neq \varnothing$, then
--   $$Z = \operatorname*{argmin}_{x\in X}\big(-\langle x, v\rangle + f(x) + g(x - v)\big) = \operatorname*{argmin}_{x\in X}\big(f(x) + g(x - v)\big).$$
--
--   The solutions of the normal problem are thus exactly the minimizers of the "normal" optimization problem $\min f + g(\cdot - v)$, which is meaningful even when $\operatorname{dom} f \cap \operatorname{dom} g = \varnothing$.
--
--   **Formalization Note** $f, g$ are `X → EReal` functions satisfying the published `GammaZero` (never $-\infty$, not identically $+\infty$, convex epigraph, lower semicontinuous); `subgrad f x` is $\partial f(x)$ (empty where $f(x) = +\infty$). The proximal maps are `Pf Pg : X → X` characterized by `IsResolvent 1 (subgrad f) Pf` ($x - P_f x \in \partial f(P_f x)$), which is $P_f = (\mathrm{Id}+\partial f)^{-1}$; $P_{f^*}$ is `resInv Pf` $= \mathrm{Id} - P_f$ (Moreau's decomposition, (8)), and $R_f$ is `refl Pf`. $v$ is the least-norm point of $\overline{\operatorname{ran}}(\mathrm{Id}-T)$. The standing assumptions of §6 (p. 22) are explicit hypotheses: (12) of p. 6, and $v_R = 0$, encoded equivalently as $0 \in \overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}$ (for a closed convex set $C$, $P_C(0) = 0 \iff 0 \in C$). By (68) $v = v_D$, so $v_D$ is not a separate variable. `CompleteSpace X` makes the space Hilbert. Each argmin is written $\{x \mid \forall y,\ F(x) \le F(y)\}$, with the real term $-\langle x, v\rangle$ cast into `EReal`.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 23, Proposition 6.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

/-- Proposition 6.2, p. 23, under the standing assumptions of §6 (p. 22):
(i) `Z = {x | 0 ∈ ∂f(x) + ∂g(x − v)}`;
(ii) `Z ≠ ∅ ⇒ Z = argmin(−⟨·, v⟩ + f + g(· − v)) = argmin(f + g(· − v))`. -/
theorem proposition_6_2 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g))) :
    solZ (subgrad f) (subgrad g) v =
        {x | ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g (x - v), a + b = 0} ∧
    ((solZ (subgrad f) (subgrad g) v).Nonempty →
      solZ (subgrad f) (subgrad g) v =
          {x | ∀ y, ((-⟪x, v⟫_ℝ : ℝ) : EReal) + f x + g (x - v) ≤
            ((-⟪y, v⟫_ℝ : ℝ) : EReal) + f y + g (y - v)} ∧
        solZ (subgrad f) (subgrad g) v = {x | ∀ y, f x + g (x - v) ≤ f y + g (y - v)}) := by sorry

end InconsistentDR.Shadow
