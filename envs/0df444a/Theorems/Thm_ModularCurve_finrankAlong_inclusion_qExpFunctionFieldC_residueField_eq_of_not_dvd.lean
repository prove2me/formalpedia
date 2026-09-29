-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd
-- name    : ModularCurve.finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/36eb14e3-6c8f-58ac-ae1f-94fff22b78ea
-- title:
--   Reduction at p ∤ Mℓ of the T_ℓ degeneracy maps
-- statement:
--   Let $M,\ell \ge 1$ and let $p$ be prime with $p \nmid M\ell$, let $P$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that $p$ belongs to the nonunits of $P$, and write $k$ for the residue field of $P$. For a field $K$ and $\Gamma \le \mathrm{SL}_2(\mathbb Z)$, [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) denotes the intermediate field of $K((q))$ generated over $K$ by the ratios $\mathrm{intSeriesC}\,K\,p_f/\mathrm{intSeriesC}\,K\,p_g$, where $f,g$ are modular forms of one weight on $\Gamma$ with integral $q$-expansions $p_f,p_g$ and the denominator is nonzero. With $\bar\alpha$ the inclusion of $F_k(\Gamma_1(M))$ into $F_k(\Gamma_1(M) \cap \Gamma_0(M\ell))$ coming from $\Gamma_1(M) \cap \Gamma_0(M\ell) \le \Gamma_1(M)$, the assertion is fourfold: the larger field is a finite module over the smaller along $\bar\alpha$; it is a separable algebra over it; its degree along $\bar\alpha$ equals the degree along [`ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ`](def/ModularCurve_X1HeckeOperator.html#L66), the corresponding inclusion of the $\overline{\mathbb Q}$-base changes (adjoining the coefficientwise images) of the rational function fields `x1FunctionFieldC ℚ M` and `qExpFunctionFieldC ℚ (Γ₁(M) ⊓ Γ₀(Mℓ))`; and there is a $k$-algebra map $\beta$ between the same two fields acting on Laurent series as [`ModularCurve.qExpand k ℓ`](def/ModularCurve_X0.html#L25), which multiplies all exponents by $\ell$ (i.e. $q \mapsto q^{\ell}$), such that the target is finite over the source along $\beta$.
--
--   This records the behaviour at a place above $p \nmid M\ell$ of the two degeneracy maps $X(\Gamma_1(M) \cap \Gamma_0(M\ell)) \to X_1(M)$ underlying the Hecke correspondence $T_\ell$: the forgetful map reduces to a finite separable map of the special fibres of the generic degree, and the second map, given on $q$-expansions by $q \mapsto q^{\ell}$, is defined and finite in characteristic $p$. It feeds the computation of the reduction of the Hecke operator modulo $p$ in [`ModularCurve.reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne`](thm.html#ModularCurve.reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne), on the way to the Eichler–Shimura congruence relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd
    (M p ℓ : ℕ) [NeZero M] [NeZero ℓ] [Fact p.Prime] (hpMℓ : ¬ p ∣ M * ℓ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    AlgebraicCurve.FiniteAlong (IsLocalRing.ResidueField P)
        (IntermediateField.inclusion
          (ModularCurve.qExpFunctionFieldC_mono (IsLocalRing.ResidueField P)
            (inf_le_left : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) ≤
              CongruenceSubgroup.Gamma1 M))) ∧
      AlgebraicCurve.SeparableAlong (IsLocalRing.ResidueField P)
        (IntermediateField.inclusion
          (ModularCurve.qExpFunctionFieldC_mono (IsLocalRing.ResidueField P)
            (inf_le_left : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) ≤
              CongruenceSubgroup.Gamma1 M))) ∧
      AlgebraicCurve.finrankAlong (IsLocalRing.ResidueField P)
          (IntermediateField.inclusion
            (ModularCurve.qExpFunctionFieldC_mono (IsLocalRing.ResidueField P)
              (inf_le_left : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) ≤
                CongruenceSubgroup.Gamma1 M))) =
        AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ)
          (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) ∧
      ∃ β : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M)
          →ₐ[IsLocalRing.ResidueField P]
          ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P)
            (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)),
        (∀ x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M),
            (β x : LaurentSeries (IsLocalRing.ResidueField P)) =
              ModularCurve.qExpand (IsLocalRing.ResidueField P) ℓ
                (x : LaurentSeries (IsLocalRing.ResidueField P))) ∧
          AlgebraicCurve.FiniteAlong (IsLocalRing.ResidueField P) β := by sorry
