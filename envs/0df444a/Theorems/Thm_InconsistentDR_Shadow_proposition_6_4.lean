-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_proposition_6_4
-- name    : InconsistentDR.Shadow.proposition_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:44.910998+00:00
-- url     : https://prove2.me/theorems/e62dded0-b3e2-4ee6-9a4d-9ab7d76cdd17
-- title:
--   Proposition 6.4, p. 24 — ε_n → 0, δ_n → 0, and f(y) + g(y − v) ≥ f(P_f Tⁿx) + g(P_g R_f Tⁿx) + ε_n + δ_n for n ≥ 1
-- statement:
--   Throughout, $X$ is a real Hilbert space, $f, g \in \Gamma_0(X)$ (proper, convex, lower semicontinuous, with values in $]-\infty,+\infty]$), $(A,B) = (\partial f, \partial g)$, $P_f = (\mathrm{Id}+\partial f)^{-1}$ and $P_g$ are the proximal mappings, $R_f = 2P_f - \mathrm{Id}$, $P_{f^*} = \mathrm{Id} - P_f$, and
--   $$T = \mathrm{Id} - P_f + P_g R_f$$
--   is the Douglas–Rachford operator (69). The vector $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$ is the minimal displacement vector of $T$, the standing assumption (12) $\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}$ holds, and $v_R = P_{\overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}}(0) = 0$ (68). In addition $Z \neq \varnothing$ (74).
--
--   Let $y \in \operatorname{dom}f \cap (v + \operatorname{dom}g)$ and $x \in X$, and for $n \in \mathbb N$ set
--   $$\epsilon_n = \langle y - P_g R_f T^n x - v,\ P_f T^n x - P_g R_f T^n x - v\rangle,$$
--   $$\delta_n = \langle P_f T^n x - P_g R_f T^n x - v,\ P_f T^n x - (T^n x + n v)\rangle .$$
--   Then $\epsilon_n \to 0$ and $\delta_n \to 0$, and
--   $$f(y) + g(y - v) \ge f(P_f T^n x) + g(P_g R_f T^n x) + \epsilon_n + \delta_n \qquad (n \ge 1).$$
--
--   The estimate says that the shadow pair $(P_f T^n x, P_g R_f T^n x)$ is asymptotically at least as good as any feasible point of the normal problem; it drives the value convergence in Proposition 6.5.
--
--   **Formalization Note** $f, g$ are `X → EReal` functions satisfying the published `GammaZero` (never $-\infty$, not identically $+\infty$, convex epigraph, lower semicontinuous); `subgrad f x` is $\partial f(x)$ (empty where $f(x) = +\infty$). The proximal maps are `Pf Pg : X → X` characterized by `IsResolvent 1 (subgrad f) Pf` ($x - P_f x \in \partial f(P_f x)$), which is $P_f = (\mathrm{Id}+\partial f)^{-1}$; $P_{f^*}$ is `resInv Pf` $= \mathrm{Id} - P_f$ (Moreau's decomposition, (8)), and $R_f$ is `refl Pf`. $v$ is the least-norm point of $\overline{\operatorname{ran}}(\mathrm{Id}-T)$. The standing assumptions of §6 (p. 22) are explicit hypotheses: (12) of p. 6, and $v_R = 0$, encoded equivalently as $0 \in \overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}$ (for a closed convex set $C$, $P_C(0) = 0 \iff 0 \in C$). By (68) $v = v_D$, so $v_D$ is not a separate variable. `CompleteSpace X` makes the space Hilbert. The additional standing assumption (74) of p. 24, $Z \neq \varnothing$, is the hypothesis `hZ`, with $Z$ = `solZ (subgrad f) (subgrad g) v` $= \{x \mid 0 \in -v + \partial f(x) + \partial g(x - v)\}$ (14). $\epsilon$ and $\delta$ are local definitions (`let`) inside the statement; $n v$ is $(n : \mathbb R)\cdot v$.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 24, Proposition 6.4, (76a), (76b), (77), (78)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

/-- Proposition 6.4, p. 24, under the standing assumptions of §6 and (74) (`Z ≠ ∅`). For
`y ∈ dom f ∩ (v + dom g)` and `x ∈ X`, set
`εₙ = ⟨y − P_g R_f Tⁿx − v, P_f Tⁿx − P_g R_f Tⁿx − v⟩` (76a) and
`δₙ = ⟨P_f Tⁿx − P_g R_f Tⁿx − v, P_f Tⁿx − (Tⁿx + n v)⟩` (76b). Then `εₙ → 0`, `δₙ → 0` (77) and
`f(y) + g(y − v) ≥ f(P_f Tⁿx) + g(P_g R_f Tⁿx) + εₙ + δₙ` for all `n ≥ 1` (78). -/
theorem proposition_6_4 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)))
    (hZ : (solZ (subgrad f) (subgrad g) v).Nonempty)
    (y : X) (hy : y ∈ edom f ∧ y - v ∈ edom g) (x : X) :
    let ε : ℕ → ℝ := fun n =>
      ⟪y - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v,
        Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v⟫_ℝ
    let δ : ℕ → ℝ := fun n =>
      ⟪Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v,
        Pf ((drT Pf Pg)^[n] x) - ((drT Pf Pg)^[n] x + (n : ℝ) • v)⟫_ℝ
    Tendsto ε atTop (𝓝 0) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n →
        f (Pf ((drT Pf Pg)^[n] x)) + g (Pg (refl Pf ((drT Pf Pg)^[n] x))) +
            ((ε n + δ n : ℝ) : EReal) ≤ f y + g (y - v) := by sorry

end InconsistentDR.Shadow
