-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Coding_stream_mem_interior
-- name    : OAI.BalancedTransport.Coding.stream_mem_interior
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:07:48.984988+00:00
-- url     : https://prove2.me/theorems/54272de2-3b4a-4144-89e6-e609a4e81b28
-- title:
--   Stream codes with interior digits lie in the open unit interval
-- statement:
--   Let $B>0$ and let $\delta:S\to\{0,\dots,B-1\}$ satisfy $0<\delta(a)$ and $\delta(a)+1<B$ for every letter $a$. For a stream $s=(s_0,s_1,\dots)$ of letters, the base-$B$ code
--   $$
--   c(s)=\sum_{n\ge0}\delta(s_n)B^{-(n+1)}
--   $$
--   lies in the open interval $(0,1)$.
--
--   With odd digits $2j+1$ in base $2|S|+1$ both conditions hold, so coded configurations lie strictly inside their boxes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/PrefixCoding.lean#L282-L295

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding

open OAI OAI.BalancedTransport OAI.BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem OAI.BalancedTransport.Coding.stream_mem_interior {B : ℕ} (hB : 0 < B) (digit : S → Fin B)
    (hlo : ∀ a, 0 < (digit a : ℝ)) (hhi : ∀ a, (digit a : ℝ) + 1 < B)
    (s : Stream' S) : stream digit s ∈ Set.Ioo (0 : ℝ) 1 := by sorry
