-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_effective_affine_force
-- name    : OAI.BalancedTransport.Effectivity.effective_affine_force
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:18:21.454982+00:00
-- url     : https://prove2.me/theorems/a591d4ff-d9ca-493a-9367-bc68bcc79051
-- title:
--   Effectivity of the force $f_0+\nu f_1$ relative to a name of $\nu$
-- statement:
--   Let $O$ be a set of oracles. A velocity is effective relative to $O$ when there are $O$-computable maps $E$ and $b$ such that, for every multi-index $a$, rational point $(t,x)$ with $t\ge0$ and $n\in\mathbb N$, $E(a,(t,x),n)$ approximates $\partial^av(t,x)$ within $2^{-n}$, and $|\partial^av|\le b(a)$ for $t\ge0$. Let $v,w$ be effective relative to $O$, and let $\nu$ have an $O$-computable name $q_n\in\mathbb Q$, with $|q_n-\nu|\le2^{-n}$. Assume
--   $$
--   \partial^a(v+\nu w)=\partial^av+\nu\,\partial^aw\qquad(t\ge0).
--   $$
--   Then $v+\nu w$ is effective relative to $O$.
--
--   Applied to $v=f_0$ and $w=f_1$, this makes the Navier–Stokes force computable from any name of the viscosity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RelativeForce.lean#L135-L217

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity

theorem OAI.BalancedTransport.Effectivity.effective_affine_force {O : Set (ℕ →. ℕ)} {v w : Velocity} {ν : ℝ}
    (hv : EffectiveFieldIn O v) (hw : EffectiveFieldIn O w)
    {name : ℕ → ℚ} (hc : ComputableIn O name) (hn : RealName name ν)
    (hlin : ∀ a t, 0 ≤ t → ∀ x,
      mixedD a (affineForce v w ν) t x = mixedD a v t x + ν • mixedD a w t x) :
    EffectiveFieldIn O (affineForce v w ν) := by sorry
