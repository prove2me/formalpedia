-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_theorem_6_9
-- name    : InconsistentDR.Shadow.theorem_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:35.911303+00:00
-- url     : https://prove2.me/theorems/a7b93f4e-5f44-40a8-bc9a-ca9ef265a2ed
-- title:
--   Theorem 6.9, p. 28 — the primal Douglas–Rachford shadows converge weakly, and in value, to a minimizer of the normal problem f + g(· − v)
-- statement:
--   Let $X$ be a real Hilbert space and $f, g \in \Gamma_0(X)$. Let $P_f = (\mathrm{Id} + \partial f)^{-1}$ and $P_g$ be the proximal mappings, $R_f = 2P_f - \mathrm{Id}$, and let
--   $$T = \mathrm{Id} - P_f + P_g R_f$$
--   be the Douglas–Rachford operator, with minimal displacement vector $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$. Assume the standing assumption (12) of the paper, $\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D \cap R} = \overline{D} \cap \overline{R}$ with $D = \operatorname{dom}\partial f - \operatorname{dom}\partial g$ and $R = \operatorname{ran}\partial f + \operatorname{ran}\partial g$. Suppose that
--   1. $0 \in \operatorname{dom} f^* + \operatorname{dom} g^*$;
--   2. $v \in \operatorname{ran}(\mathrm{Id} - T)$;
--   3. $\operatorname{zer}(\partial f + \partial g(\cdot - v)) \neq \varnothing$.
--
--   Set $\mu = \min_{x\in X}\big(f(x) + g(x - v)\big)$ and let $x \in X$. Then there is $\bar z \in X$ such that
--   1. $P_f T^n x \rightharpoonup \bar z$, and $\bar z$ minimizes $f + g(\cdot - v)$;
--   2. $P_g R_f T^n x \rightharpoonup \bar z - v$, and $\bar z - v$ minimizes $f(\cdot + v) + g$;
--   3. $$f(P_f T^n x) + g(P_g R_f T^n x) \to f(\bar z) + g(\bar z - v) = \mu ;$$
--   4. $f(P_f T^n x) \to f(\bar z)$;
--   5. $g(P_g R_f T^n x) \to g(\bar z - v)$.
--
--   When $\operatorname{dom} f \cap \operatorname{dom} g = \varnothing$ the problem $\min f + g$ has no solution and the iterates $T^n x$ diverge, but their primal shadows still converge to a solution of the normal problem $\min f + g(\cdot - v)$, the "least inconsistent" shift of the original problem.
--
--   **Formalization Note** $f, g$ are `X → EReal` functions satisfying the published `GammaZero`; `subgrad` is $\partial$. The proximal maps are `Pf Pg : X → X` characterized by `IsResolvent 1 (subgrad f) Pf` ($x - P_f x \in \partial f(P_f x)$), i.e. $P_f = (\mathrm{Id}+\partial f)^{-1}$; $R_f$ is `refl Pf`. $v$ is the least-norm point of $\overline{\operatorname{ran}}(\mathrm{Id}-T)$. The standing assumption (12) (p. 6) is restored as a hypothesis; the paper assumes it "from this point onwards", and the proof uses it through Proposition 3.3(vii) (it holds automatically when $X$ is finite-dimensional, Remark 2.3). The page prints $\mu := \min_x(f(x+v) - g(x))$; this is a typo, and the statement uses $\mu = \min_x (f(x) + g(x-v))$ as in Proposition 6.5 and §1.1 (equivalently $\min_x (f(x+v) + g(x))$), written as the `EReal` infimum $\inf_y (f(y) + g(y - v))$, which item 3 shows is attained. $\operatorname{zer}(\partial f + \partial g(\cdot - v)) \neq \varnothing$ is written $\exists x, a, b$ with $a \in \partial f(x)$, $b \in \partial g(x - v)$, $a + b = 0$. Item 2's minimality is stated literally for $\bar z - v$, i.e. with $f((\bar z - v) + v)$. Weak convergence is the published `IsWeakLimit`. `CompleteSpace X` makes the space Hilbert.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 28, Theorem 6.9

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

/-- Theorem 6.9, p. 28 (main result: primal shadows converge), under the standing assumption
(12). Let `f, g ∈ Γ₀(X)` with `0 ∈ dom f* + dom g*`, `v ∈ ran(Id − T)` and
`zer(∂f + ∂g(· − v)) ≠ ∅`; let `µ := min_x (f(x) + g(x − v))` (the printed
`min (f(x + v) − g(x))` is corrected). For every `x` there is `z̄` with
(i) `P_f Tⁿx ⇀ z̄`, a minimizer of `f + g(· − v)`;
(ii) `P_g R_f Tⁿx ⇀ z̄ − v`, a minimizer of `f(· + v) + g`;
(iii) `f(P_f Tⁿx) + g(P_g R_f Tⁿx) → f(z̄) + g(z̄ − v) = µ`;
(iv) `f(P_f Tⁿx) → f(z̄)`; (v) `g(P_g R_f Tⁿx) → g(z̄ − v)`. -/
theorem theorem_6_9 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (h0 : (0 : X) ∈ domConj f + domConj g)
    (hvran : v ∈ Set.range fun x => x - drT Pf Pg x)
    (hzer : ∃ x, ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g (x - v), a + b = 0)
    (x : X) :
    ∃ z : X,
      (IsWeakLimit (fun n => Pf ((drT Pf Pg)^[n] x)) z ∧
        ∀ y, f z + g (z - v) ≤ f y + g (y - v)) ∧
      (IsWeakLimit (fun n => Pg (refl Pf ((drT Pf Pg)^[n] x))) (z - v) ∧
        ∀ y, f (z - v + v) + g (z - v) ≤ f (y + v) + g y) ∧
      (Tendsto (fun n => f (Pf ((drT Pf Pg)^[n] x)) + g (Pg (refl Pf ((drT Pf Pg)^[n] x))))
          atTop (𝓝 (f z + g (z - v))) ∧
        f z + g (z - v) = ⨅ y, f y + g (y - v)) ∧
      Tendsto (fun n => f (Pf ((drT Pf Pg)^[n] x))) atTop (𝓝 (f z)) ∧
      Tendsto (fun n => g (Pg (refl Pf ((drT Pf Pg)^[n] x)))) atTop (𝓝 (g (z - v))) := by sorry

end InconsistentDR.Shadow
