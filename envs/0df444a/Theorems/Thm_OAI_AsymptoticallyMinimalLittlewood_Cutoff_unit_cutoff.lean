-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Cutoff_unit_cutoff
-- name    : OAI.AsymptoticallyMinimalLittlewood.Cutoff.unit_cutoff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:57:06.672976+00:00
-- url     : https://prove2.me/theorems/33849472-504a-437b-8de7-f5db09ff6eef
-- title:
--   Smooth cutoffs supported strictly inside $(-\tfrac12,\tfrac12)$ with squared mass arbitrarily close to $1$
-- statement:
--   Let $\varepsilon>0$. Then there exists a function $g:\mathbb{R}\to\mathbb{R}$ with the following four properties.
--
--   1. $g$ is infinitely differentiable and has compact support.
--   2. There is a number $\alpha$ with $0<\alpha<\tfrac12$ such that the closed support $\operatorname{tsupp} g=\overline{\{x\in\mathbb{R}: g(x)\neq 0\}}$ is contained in $[-\alpha,\alpha]$.
--   3. $0\le g(x)\le 1$ for every $x\in\mathbb{R}$.
--   4. The squared mass of $g$ exceeds $1-\varepsilon$:
--
--   $$
--   \int_{\mathbb{R}} g(x)^2\,dx>1-\varepsilon .
--   $$
--
--   Since $0\le g\le 1$ and $g$ vanishes outside an interval of length $2\alpha<1$, the squared mass of such a function is always less than $1$; the theorem says that this bound can be approached arbitrarily closely by smooth cutoffs whose support stays strictly inside the open interval $(-\tfrac12,\tfrac12)$. Such a $g$ fits into one period of the circle $\mathbb{R}/\mathbb{Z}$ without touching the endpoints $\pm\tfrac12$, which is how it serves as the smooth window in the Fourier-spreading and sampling constructions.
--
--   **Formalization Note** Smoothness is `ContDiff` of order infinity, the support condition is stated for the topological support `tsupport g`, and the integral is the Lebesgue (Bochner) integral over the real line.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Cutoff.lean#L35-L53

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket

open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Set
open scoped Topology ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.Cutoff.unit_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∃ α : ℝ, 0 < α ∧ α < 1/2 ∧ tsupport g ⊆ Icc (-α) α) ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      1-ε < ∫ x : ℝ, g x ^ 2 := by sorry
