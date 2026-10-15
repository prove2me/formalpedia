-- Prove2me | Theorems.Thm_OAI_BufferedIsing_DSS_interpolation
-- name    : OAI.BufferedIsing.DSS.interpolation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:24:38.72155+00:00
-- url     : https://prove2.me/theorems/54d6ff95-04b6-422b-aade-63521a85f25c
-- title:
--   Interpolation inequality for the hyperbolic-tangent field update
-- statement:
--   For real numbers $x,y$ let $\operatorname{upd}(x,y)=\dfrac{x+y}{1+xy}$ denote the single-spin field update; it is the addition law of the hyperbolic tangent, $\operatorname{upd}(\tanh p,\tanh q)=\tanh(p+q)$.
--
--   **Theorem.** Let $a,b,c,z\in\mathbb{R}$ satisfy $-1<a<1$, $-1<b<1$, $b\le a$, $0\le c<1$, $z\ge0$ and $a-b\le2z$, and put $\alpha=\dfrac{1-c}{1+zc}$. Then there exists $d$ with $-1<d<1$ such that
--   $$
--   \operatorname{upd}(a,c)\le\alpha\,\operatorname{upd}(a,d)+(1-\alpha)\qquad\text{and}\qquad\alpha\,\operatorname{upd}(b,d)-(1-\alpha)\le\operatorname{upd}(b,-c).
--   $$
--
--   In the Ising application, $a$ and $b$ are the magnetizations at a site $v$ under two fields $g+h$ and $g-h$, $z$ is the magnetization at $v$ under $h$ alone, and $c=\tanh t$ for a field increment $t\ge0$ at $v$. Adding a field $r$ at $v$ changes the magnetization $x$ at $v$ into $\operatorname{upd}(x,\tanh r)$, so the lemma supplies one common intermediate field $s=\operatorname{artanh}d$ such that raising the field at $v$ by $t$ in the first system is dominated by the $\alpha$-mixture of raising it by $s$ and pinning the spin to $+1$, while lowering it by $t$ in the second system dominates the $\alpha$-mixture of raising it by $s$ and pinning the spin to $-1$. The weight $\alpha$ is the one for which the corresponding statement holds with equality in the reference system of magnetization $z$.
--
--   **Formalization Note** $\operatorname{upd}(x,y)$ is `update x y`, defined as `(x + y) / (1 + x * y)` with Lean's convention $x/0=0$. Under the hypotheses all denominators that occur ($1+ac$, $1+ad$, $1+bd$, $1-bc$ and $1+zc$) are positive, so the convention plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Interpolation.lean#L97-L147

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation

open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical

theorem OAI.BufferedIsing.DSS.interpolation {a b c z : ℝ}
    (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1)
    (hab : b ≤ a) (hc : 0 ≤ c ∧ c < 1)
    (hz : 0 ≤ z) (hgap : a - b ≤ 2 * z) :
    ∃ d : ℝ, -1 < d ∧ d < 1 ∧
      update a c ≤ ((1 - c) / (1 + z * c)) * update a d +
        (1 - (1 - c) / (1 + z * c)) ∧
      ((1 - c) / (1 + z * c)) * update b d -
        (1 - (1 - c) / (1 + z * c)) ≤ update b (-c) := by sorry
