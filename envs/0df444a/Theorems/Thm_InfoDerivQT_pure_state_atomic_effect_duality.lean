-- Prove2me | Theorems.Thm_InfoDerivQT_pure_state_atomic_effect_duality
-- name    : InfoDerivQT.pure_state_atomic_effect_duality
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T11:50:44.445771+00:00
-- url     : https://prove2.me/theorems/c128ef78-e7e6-49eb-83ea-db70d814a1fe
-- title:
--   Theorem 8 — every pure state has a unique atomic effect with $(a|\varphi)=1$
-- statement:
--   Let $T$ satisfy the six principles, $A$ a system, and $\varphi\in\mathrm{St}_1(A)$ a pure normalized state. Then there is exactly one atomic effect $a\in\mathrm{Eff}(A)$ such that
--
--   $$(a|\varphi)=1.$$
--
--   Together with Theorem 7 this establishes the duality between pure states and normalized atomic effects.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-16, Sec. VI, Theorem 8

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem pure_state_atomic_effect_duality (T : OPT) (hT : T.SatisfiesPrinciples) (A : T.Sys)
    (φ : Vec (T.size A)) (hφ₁ : φ ∈ T.St1 A) (hφ : T.IsPure A φ) :
    ∃! a : Module.Dual ℝ (Vec (T.size A)), T.IsAtomicEff A a ∧ a φ = 1 := by sorry
end InfoDerivQT
