-- Prove2me | Theorems.Thm_ModularCurve_exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd
-- name    : ModularCurve.exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/af5ac459-dbcd-5a72-bf27-4d236145c90a
-- title:
--   Two regular prolongations above q∤ M, and no third
-- statement:
--   Fix an integer $M\neq 0$, a subgroup $H\le(\mathbb{Z}/M)^\times$, a prime $q$ with $q\nmid M$, and a valuation subring $A\subseteq\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$ (`LiesOverPrime`); write $k=\mathrm{ResidueField}\,A$. Put $E=$ `laurentBaseChange` of the $q$-expansion function field `xHTopFunctionFieldC ℚ M H (M*q)` of $\Gamma_H(M)\cap\Gamma_0(Mq)$, i.e. the subfield of $\overline{\mathbb{Q}}((\mathsf q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of that rational field, and $\overline F=$ `xHFunctionFieldC k M H`. The assertion is the existence of a pair $R_0,R_1$ of `RegularProlongation`s of $A$ to $E$ with residue field target $\overline F$ (each: a valuation subring `integers` of $E$ meeting $\overline{\mathbb{Q}}$ exactly in $A$, with a surjective residue homomorphism onto $\overline F$ whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every nonzero $f\in E$ has a scalar multiple in `integers` with nonzero residue), together with a $\overline{\mathbb{Q}}$-automorphism $w$ of $E$, such that: $w\circ\mathtt{heckeAlphaHBar}=\mathtt{heckeBetaHBar}$ and $w\circ\mathtt{heckeBetaHBar}=\mathtt{heckeAlphaHBar}\circ\langle q\rangle$ on the base change to $\overline{\mathbb{Q}}$ of the level-$\Gamma_H(M)$ function field, where $\langle q\rangle=$ `diamondAutHBar` at the unit $q\bmod M$; $R_0$ is the Gauss ring, $f\in(R_0)$`.integers` iff $f=x/y$ with $x,y$ Laurent series over $A$ and $y$ having nonzero coefficientwise reduction; every Laurent series over $A$ lying in $E$ belongs to $(R_0)$`.integers` with residue its coefficientwise reduction in $k((\mathsf q))$; $f\in(R_1)$`.integers` iff $wf\in(R_0)$`.integers`, with equal residues; $(R_0)$`.integers`$\neq(R_1)$`.integers`; for every $f\in E$ whose Laurent series is `jqModC` over $\overline{\mathbb{Q}}$, $f$ lies in both rings, its $R_0$-residue is `jqModC` over $k$ and its $R_1$-residue is `jqModC`$^q$, with $[\overline F:k((R_1)\text{-residue})]=q\,[\overline F:k((R_0)\text{-residue})]$ and $[E:\overline{\mathbb{Q}}(f)]=(q+1)\,[\overline F:k((R_0)\text{-residue})]$; and finally, for such $f$, any valuation subring $V$ of $E$ that agrees with $(R_0)$`.integers` on the subfield $\overline{\mathbb{Q}}(f)$ equals $(R_0)$`.integers` or $(R_1)$`.integers`.
--
--   This is the valuation-theoretic form of the Deligne–Rapoport description of the reduction at $q\nmid M$ of the modular curve of level $\Gamma_H(M)\cap\Gamma_0(q)$: the special fibre has exactly two components, the one through the cusp $\infty$ and its Atkin–Lehner transform, both birational to $X_H(M)$ over $k$ and of degrees $d$ and $qd$ over the $j$-line. It is used in [`ModularCurve.exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd`](thm.html#ModularCurve.exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd) on the way to the congruence relation for the Hecke operator $T_q$ in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {q : ℕ} [Fact q.Prime] (hqM : ¬ q ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ (R : Fin 2 → AlgebraicCurve.RegularProlongation A
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))
        (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H))
      (w : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)) ≃ₐ[AlgebraicClosure ℚ]
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),

      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H q x) =
            ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H q x) ∧
      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H q x) =
            ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H q
              (ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime q ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM)) x)) ∧

      (∀ f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)),
        f ∈ (R 0).integers ↔
          ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y =
              ModularCurve.coeffMap A.subtype x) ∧

      (∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),
        ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))) ∈ (R 0).integers,
          (((R 0).residue ⟨_, hint⟩ :
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y) ∧

      (∀ f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)),
        f ∈ (R 1).integers ↔ w f ∈ (R 0).integers) ∧
      (∀ (f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))
        (h₁ : f ∈ (R 1).integers) (h₀ : w f ∈ (R 0).integers),
        (R 1).residue ⟨f, h₁⟩ = (R 0).residue ⟨w f, h₀⟩) ∧

      (R 0).integers ≠ (R 1).integers ∧

      (∀ (f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
        ∃ hj : ∀ i, f ∈ (R i).integers,
          (((R 0).residue ⟨f, hj 0⟩ :
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.jqModC (IsLocalRing.ResidueField A) ∧
          (((R 1).residue ⟨f, hj 1⟩ :
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.jqModC (IsLocalRing.ResidueField A) ^ q ∧
          Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              {(R 1).residue ⟨f, hj 1⟩})
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) =
          q * Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              {(R 0).residue ⟨f, hj 0⟩})
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) ∧
          Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({f} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
                (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))))
            (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))) =
          (q + 1) * Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              {(R 0).residue ⟨f, hj 0⟩})
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)) ∧

      ∀ (f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
        ∀ V : ValuationSubring (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),
          (∀ e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({f} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
                (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))),
            e ∈ V ↔ e ∈ (R 0).integers) →
          V = (R 0).integers ∨ V = (R 1).integers := by sorry
