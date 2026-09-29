-- Prove2me | Theorems.Thm_NonsmoothNewton_Local_prop_2_1
-- name    : NonsmoothNewton.Local.prop_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:01:19.505385+00:00
-- url     : https://prove2.me/theorems/c4ef752c-0761-4d17-b5d2-1987230f1f61
-- title:
--   Proposition 2.1 — the limit of $Vh$ over $V\in\partial F(x+th)$ is the directional derivative
-- statement:
--   Let $E$, $G$ be finite-dimensional real normed spaces and $F : E \to G$ locally Lipschitz. Fix $x, h \in E$ and suppose the limit
--
--   $$
--   L = \lim_{\substack{V \in \partial F(x+th) \\ t \downarrow 0}} \{V h\} \tag{2.3}
--   $$
--
--   exists, i.e. for every $\varepsilon > 0$ there is $\delta > 0$ with $\|Vh - L\| < \varepsilon$ whenever $0 < t < \delta$ and $V \in \partial F(x+th)$. Then the classic directional derivative exists and equals this limit:
--
--   $$
--   F'(x;h) = \lim_{t\downarrow 0}\frac{F(x+th)-F(x)}{t} = L .
--   $$
--
--   This identifies the directional derivative of a semismooth map with a limit of generalized-Jacobian actions, which is the bridge between the definition of semismoothness and its characterizations.
--
--   **Formalization Note** The paper assumes (2.3) for every $h$ and concludes (2.4)–(2.5) for every $h$; the statement here is the same assertion for each fixed direction $h$ separately (the proof in the paper is direction by direction). The paper's $\mathbb R^n \to \mathbb R^m$ is generalised to finite-dimensional normed spaces; Section 2's standing assumption "F locally Lipschitzian" is a hypothesis.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 355, Proposition 2.1 (with assumption (2.3), p. 354)

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Proposition 2.1, p. 355. If `F` is locally Lipschitz and, for the direction
`h`, the limit (2.3) `L = lim_{V ∈ ∂F(x + t h), t ↓ 0} V h` exists, then the one-sided
directional derivative `F'(x; h)` (2.4) exists and equals `L` (2.5). -/
theorem prop_2_1 {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x h : E) (L : G)
    (hL : ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + t • h), ‖V h - L‖ < ε) :
    HasDirDerivAt F x h L := by sorry

end NonsmoothNewton.Local
