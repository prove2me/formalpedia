-- Prove2me | Theorems.Thm_ModularCurve_exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq
-- name    : ModularCurve.exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/7f6b0d42-5c25-5ef8-93f6-8cc73b9dd793
-- title:
--   Unit-root factor of Tₚ on TₚJ₁(M) and p-rank
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime with $p\nmid M$, and let $K$ be a field of characteristic zero equipped with a $\mathbb{Z}_p$-algebra structure. Give $J_1(M)=\mathrm{Pic}^0$ of the function field `x1FunctionFieldBar M` over $\overline{\mathbb{Q}}$ (degree-zero divisors modulo principal ones) the module structure over `HeckeAlgOne` $=\mathbb{Z}[X_{\ell},X_n]$ provided by `heckeModuleOneBar M` (the action through `heckeEvalOneBar` when the diamond-commutation predicate `HeckeDiamondCommuteBar M` holds, and otherwise the action in which every variable acts as $0$). Write $T$ for the Tate module of sequences $(x_n)$ in $J_1(M)$ with $p^n x_n=0$ and $px_{n+1}=x_n$, a $\mathbb{Z}_p$-module, let $T_p$ denote the endomorphism of $T$ induced by the generator `heckeGenOne ⟨p, _⟩` $=X_{\mathrm{inl}\,p}$, and let $V=K\otimes_{\mathbb{Z}_p}T$ with the base-changed endomorphism. The assertion is: for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $P$, there are monic $P_u,P_n\in\mathbb{Z}_p[X]$ with $P_u(0)$ a unit, $P_n\equiv X^{\deg P_n}\pmod p$, such that $(P_uP_n)$, mapped into $K[X]$, annihilates the base-changed $T_p$ on $V$, and $$p^{\,\dim_K\ker\big(P_u(T_p)\mid V\big)}=\#\big\{y\in \mathrm{Pic}^0(\mathrm{x1FunctionFieldC}\text{ of }M\text{ over }\kappa(P)):py=0\big\}^2,$$ where $\kappa(P)$ is the residue field of $P$.
--
--   This is the comparison between the unit-root (ordinary) part of $T_p$ acting on the $p$-adic Tate module of $J_1(M)$ and the $p$-rank of the reduction of $J_1(M)$ at a place above $p$: the multiplicity of the unit factor equals twice the $p$-rank, here packaged as a Hensel factorisation $P_uP_n$ annihilating $K\otimes T$. It is used in [`ModularCurve.finrank_map_reductionKernelSpan_tateModule_jOne_le_one_of_isUnit`](thm.html#ModularCurve.finrank_map_reductionKernelSpan_tateModule_jOne_le_one_of_isUnit) on the way to the local behaviour at $p$ of the Galois representations attached to weight-two forms of level $\Gamma_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq.lean

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

theorem ModularCurve.exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K] :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ Pu Pn : Polynomial ℤ_[p], Pu.Monic ∧ Pn.Monic ∧ IsUnit (Pu.coeff 0) ∧
        Pn.map (PadicInt.toZMod (p := p)) = Polynomial.X ^ Pn.natDegree ∧
        Polynomial.aeval
            ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M)
              (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).baseChange K)
            ((Pu * Pn).map (algebraMap ℤ_[p] K)) = 0 ∧
        p ^ Module.finrank K
            ↥(LinearMap.ker (Polynomial.aeval
              ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M)
                (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).baseChange K)
              (Pu.map (algebraMap ℤ_[p] K)))) =
          (Nat.card {y : ModularCurve.JOneC M (IsLocalRing.ResidueField P) // p • y = 0}) ^ 2 := by sorry
