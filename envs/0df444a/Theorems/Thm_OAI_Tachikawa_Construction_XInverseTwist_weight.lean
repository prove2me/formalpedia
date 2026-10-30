-- Prove2me | Theorems.Thm_OAI_Tachikawa_Construction_XInverseTwist_weight
-- name    : OAI.Tachikawa.Construction.XInverseTwist_weight
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:18:58.503451+00:00
-- url     : https://prove2.me/theorems/6c16f5c9-faeb-40d0-95d2-f152393e161e
-- title:
--   OAI.Tachikawa.Construction.XInverseTwist_weight: intermediate lemma from OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Tachikawa.Construction.XInverseTwist_weight` of [lean/OAI/RingTheory/Tachikawa/Socle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Socle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Tachikawa.Construction`, with `open CategoryTheory CategoryTheory.Abelian`, `open scoped TensorProduct ModuleCat.Algebra`):
--
--   ```lean
--   lemma XInverseTwist_weight (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
--       (n : ℕ) (x : Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n) :
--       extIso (k := k) (XInverseTwistIso q H hH) (XInverseTwistIso q H hH) n
--         (x.mapExactFunctor (SymmetrizingForm.twistFunctor (sigma q H hH).symm)) =
--           H^(n/3) • x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Tachikawa.DualBimodule`, `OAI.Tachikawa.DualBimodule.instAddCommGroup`, `OAI.Tachikawa.DualBimodule.instIsScalarTower`, `OAI.Tachikawa.DualBimodule.instModule`, `OAI.Tachikawa.DualBimodule.leftModule` and `OAI.Tachikawa.DualBimodule.rightModule` (definitions bundle `OAIQ116Ta000` of this split); `OAI.Tachikawa.C`, `OAI.Tachikawa.C.instAlgebra`, `OAI.Tachikawa.C.instModule`, `OAI.Tachikawa.C.instRing`, `OAI.Tachikawa.Construction.X` and `OAI.Tachikawa.Construction.instAddCommGroupX` (definitions bundle `OAIQ116Ta001` of this split); `OAI.Tachikawa.AlgebraInduction.instPreservesFiniteColimitsModuleCatRes`, `OAI.Tachikawa.AlgebraInduction.instPreservesFiniteLimitsModuleCatRes`, `OAI.Tachikawa.Construction.E`, `OAI.Tachikawa.Construction.T`, `OAI.Tachikawa.Construction.instModuleEX`, `OAI.Tachikawa.Construction.sigma`, `OAI.Tachikawa.DualBimodule.instIsScalarTowerMulOpposite` and `OAI.Tachikawa.DualBimodule.instSMulCommClassMulOpposite` (definitions bundle `OAIQ116Ta003` of this split); `OAI.Tachikawa.SymmetrizingForm.twistFunctor` (definitions bundle `OAIQ116Ta004` of this split); `OAI.Tachikawa.extIso` (definitions bundle `OAIQ116Ta010` of this split); `OAI.Tachikawa.Construction.XInverseTwistIso` (definitions bundle `OAIQ116Ta012` of this split).
--
--   **Used by.** The proof of `OAI.Tachikawa.SourceField.sourceDelta_bijective` of this split imports it.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Socle.lean (declaration OAI.Tachikawa.Construction.XInverseTwist_weight)

import Mathlib
import Definitions.Def_OAIQ116Ta010
import Definitions.Def_OAIQ116Ta012

section

attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

variable [CharP k 2]

lemma XInverseTwist_weight (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (x : Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n) :
    extIso (k := k) (XInverseTwistIso q H hH) (XInverseTwistIso q H hH) n
      (x.mapExactFunctor (SymmetrizingForm.twistFunctor (sigma q H hH).symm)) =
        H^(n/3) • x := by
  sorry

end Tachikawa.Construction

end

end OAI
end
