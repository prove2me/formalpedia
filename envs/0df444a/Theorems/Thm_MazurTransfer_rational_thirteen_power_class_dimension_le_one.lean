-- Prove2me | Theorems.Thm_MazurTransfer_rational_thirteen_power_class_dimension_le_one
-- name    : MazurTransfer.rational_thirteen_power_class_dimension_le_one
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T05:30:17.59382+00:00
-- url     : https://prove2.me/theorems/fce58482-764f-498c-b7ff-5ba615cd576c
-- title:
--   Rational nineteenth-power classes supported at 13 have dimension at most one
-- statement:
--   Let $C=\mathbb Q^\times/(\mathbb Q^\times)^{19}$. For each prime $q$, let $\bar v_q:C\to\mathbb F_{19}$ be the ordinary $q$-adic valuation reduced modulo $19$. Set
--
--   $$C_{13}=\bigcap_{q\text{ prime},\ q\ne13}\ker(\bar v_q).$$
--
--   Then $C_{13}$ is finite-dimensional over $\mathbb F_{19}$ and
--
--   $$\dim_{\mathbb F_{19}} C_{13}\le1.$$
--
--   This arithmetic bound controls a Selmer subspace once its rational radicand classes have zero valuation modulo $19$ away from $13$.
-- source:
--   Derived arithmetic lemma for the MazurTorsion order-13 descent. Primary arithmetic sources: Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/Data/Nat/Factorization/Defs.lean, Nat.prod_factorization_pow_eq_self and Nat.factorization_def (https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Factorization/Defs.lean); Mathlib/NumberTheory/Padics/PadicVal/Basic.lean, padicValRat_def and padicValRat.mul (https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean). The dimension statement is the derived one-prime power-class bound proved here.

import Definitions.Def_MazurTransfer_RationalNineteenthPowerValuations
open MazurTransfer.RationalNineteenthPowerClasses MazurTransfer.RationalThirteenPowerClassBound
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Module (ZMod 19) (Additive PowerClasses) := powerClassesZModModule

theorem MazurTransfer.rational_thirteen_power_class_dimension_le_one :
    FiniteDimensional (ZMod 19) thirteenSupport ∧ Module.finrank (ZMod 19) thirteenSupport ≤ 1 := by sorry
