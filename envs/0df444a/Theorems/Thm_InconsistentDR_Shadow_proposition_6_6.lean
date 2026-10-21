-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_proposition_6_6
-- name    : InconsistentDR.Shadow.proposition_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:37.904817+00:00
-- url     : https://prove2.me/theorems/2f519afd-bb15-4360-9219-b5a95ece53e9
-- title:
--   Proposition 6.6, p. 26 — P_f Tⁿx and P_g R_f Tⁿx converge weakly to minimizers of f + g(· − v) and f(· + v) + g
-- statement:
--   Throughout, $X$ is a real Hilbert space, $f, g \in \Gamma_0(X)$ (proper, convex, lower semicontinuous, with values in $]-\infty,+\infty]$), $(A,B) = (\partial f, \partial g)$, $P_f = (\mathrm{Id}+\partial f)^{-1}$ and $P_g$ are the proximal mappings, $R_f = 2P_f - \mathrm{Id}$, $P_{f^*} = \mathrm{Id} - P_f$, and
--   $$T = \mathrm{Id} - P_f + P_g R_f$$
--   is the Douglas–Rachford operator (69). The vector $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$ is the minimal displacement vector of $T$, the standing assumption (12) $\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}$ holds, and $v_R = P_{\overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}}(0) = 0$ (68). In addition $Z \neq \varnothing$ (74).
--
--   Let $x \in X$. Then
--   1. the sequence $(P_f T^n x)_{n\in\mathbb N}$ converges weakly to a minimizer of $f + g(\cdot - v)$;
--   2. the sequence $(P_g R_f T^n x)_{n\in\mathbb N}$ converges weakly to a minimizer of $f(\cdot + v) + g$.
--
--   **Formalization Note** $f, g$ are `X → EReal` functions satisfying the published `GammaZero` (never $-\infty$, not identically $+\infty$, convex epigraph, lower semicontinuous); `subgrad f x` is $\partial f(x)$ (empty where $f(x) = +\infty$). The proximal maps are `Pf Pg : X → X` characterized by `IsResolvent 1 (subgrad f) Pf` ($x - P_f x \in \partial f(P_f x)$), which is $P_f = (\mathrm{Id}+\partial f)^{-1}$; $P_{f^*}$ is `resInv Pf` $= \mathrm{Id} - P_f$ (Moreau's decomposition, (8)), and $R_f$ is `refl Pf`. $v$ is the least-norm point of $\overline{\operatorname{ran}}(\mathrm{Id}-T)$. The standing assumptions of §6 (p. 22) are explicit hypotheses: (12) of p. 6, and $v_R = 0$, encoded equivalently as $0 \in \overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}$ (for a closed convex set $C$, $P_C(0) = 0 \iff 0 \in C$). By (68) $v = v_D$, so $v_D$ is not a separate variable. `CompleteSpace X` makes the space Hilbert. The additional standing assumption (74) of p. 24, $Z \neq \varnothing$, is the hypothesis `hZ`, with $Z$ = `solZ (subgrad f) (subgrad g) v` $= \{x \mid 0 \in -v + \partial f(x) + \partial g(x - v)\}$ (14). Weak convergence is the published `IsWeakLimit` ($\langle u_n, w\rangle \to \langle z, w\rangle$ for every $w$).
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 26, Proposition 6.6

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

/-- Proposition 6.6, p. 26, under the standing assumptions of §6 and (74): for `x ∈ X`,
(i) `(P_f Tⁿx)ₙ` converges weakly to a minimizer of `f + g(· − v)`;
(ii) `(P_g R_f Tⁿx)ₙ` converges weakly to a minimizer of `f(· + v) + g`. -/
theorem proposition_6_6 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)))
    (hZ : (solZ (subgrad f) (subgrad g) v).Nonempty)
    (x : X) :
    (∃ z, IsWeakLimit (fun n => Pf ((drT Pf Pg)^[n] x)) z ∧
      ∀ y, f z + g (z - v) ≤ f y + g (y - v)) ∧
    (∃ w, IsWeakLimit (fun n => Pg (refl Pf ((drT Pf Pg)^[n] x))) w ∧
      ∀ y, f (w + v) + g w ≤ f (y + v) + g y) := by sorry

end InconsistentDR.Shadow
