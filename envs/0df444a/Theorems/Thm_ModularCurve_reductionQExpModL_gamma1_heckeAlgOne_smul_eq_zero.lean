-- Prove2me | Theorems.Thm_ModularCurve_reductionQExpModL_gamma1_heckeAlgOne_smul_eq_zero
-- name    : ModularCurve.reductionQExpModL_gamma1_heckeAlgOne_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/232295d4-c900-5372-a71d-d4a8e6909711
-- title:
--   Kernel of q-expansion reduction at p∤ M is Hecke-stable
-- statement:
--   Fix a natural number $M\ge 1$ and a prime $p$ with $p\nmid M$. Give $\mathrm{JOne}\ M$ — the degree-zero divisor class group $\mathrm{Pic}^0$ of the function field $\overline{\mathbb Q}\cdot F(\Gamma_1(M))$ obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise images of the $q$-expansion function field `qExpFunctionFieldC ℚ (Gamma1 M)` inside $\overline{\mathbb Q}((q))$ — the module structure `heckeModuleOneBar M` over `HeckeAlgOne`, the polynomial ring $\mathbb Z[X_i]$ on generators indexed by $\mathrm{Primes}\sqcup\mathbb N$ (Hecke and diamond generators); this structure is the one induced by the evaluation `heckeEvalOneBar` when the generators commute, and otherwise the one in which all generators act by zero. The assertion is: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$ (i.e. $P$ lies over $p$), for every $t\in$ `HeckeAlgOne` and every $z\in\mathrm{JOne}\ M$, if the reduction homomorphism `reductionQExpModL P (Gamma1 M)` into $\mathrm{Pic}^0$ of the $q$-expansion function field over the residue field of $P$ kills $z$, then it kills $t\cdot z$. Equivalently, the kernel of reduction at $P$ is a submodule for the full Hecke–diamond action.
--
--   This is the Hecke- and diamond-equivariance of Deuring reduction of divisor classes on $X_1(M)$ at a place above $p\nmid M$, in the weak form that only concerns the kernel of the reduction map. It feeds the analysis of the $p$-adic Tate module of $J_1(M)$ modulo the kernel of reduction, used in [`ModularCurve.finrank_map_reductionKernelSpan_tateModule_jOne_le_one_of_isUnit`](thm.html#ModularCurve.finrank_map_reductionKernelSpan_tateModule_jOne_le_one_of_isUnit) and in [`ModularCurve.pow_finrank_sub_finrank_reductionKernelSpan_tateModule_jOne_eq_card_torsion_and_exists_monic_aeval_mem`](thm.html#ModularCurve.pow_finrank_sub_finrank_reductionKernelSpan_tateModule_jOne_eq_card_torsion_and_exists_monic_aeval_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_reductionQExpModL_gamma1_heckeAlgOne_smul_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem ModularCurve.reductionQExpModL_gamma1_heckeAlgOne_smul_eq_zero
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M) :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ (t : ModularCurve.HeckeAlgOne) (z : ModularCurve.JOne M),
        ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M) z = 0 →
          ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M) (t • z) = 0 := by sorry
