-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_foldl
-- name    : OAI.BalancedTransport.Effectivity.computable_foldl
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:21:22.906985+00:00
-- url     : https://prove2.me/theorems/37f671b7-db56-43ac-a66f-e78b862dc88d
-- title:
--   Left folds of computable data are computable
-- statement:
--   Let $\alpha,\beta,\sigma$ be encodable types with $\beta$ inhabited, and let $f:\alpha\to\mathrm{List}\,\beta$, $g:\alpha\to\sigma$ and $h:\alpha\to\sigma\times\beta\to\sigma$ be computable. Then the map sending $a$ to
--   $$
--   h_a(\cdots h_a(h_a(g(a),b_0),b_1)\cdots,b_{m-1}),\qquad f(a)=[b_0,\dots,b_{m-1}],
--   $$
--   the left fold of $f(a)$ with $h_a$ starting from $g(a)$, is computable.
--
--   Running a numeric program is a left fold over its operations, so this gives computability of program evaluation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericPrograms.lean#L8-L32

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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity

theorem OAI.BalancedTransport.Effectivity.computable_foldl {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    [Inhabited β] {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun s b => h a (s,b)) (g a)) := by sorry
