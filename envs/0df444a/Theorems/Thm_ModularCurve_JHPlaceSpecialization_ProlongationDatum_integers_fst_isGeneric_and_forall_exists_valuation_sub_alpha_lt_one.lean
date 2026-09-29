-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/fe93cfa7-ed32-52ff-8526-7402745bfeaf
-- title:
--   R₁ ∩ ℚ̄ = A, units Q(j), and level-lowering residues
-- statement:
--   Fix natural numbers $p$, $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and divisibility hypotheses $p \mid M$, $p^2 \nmid M$ (with $M/p \neq 0$), together with the hypothesis that every unit of $\mathbb{Z}/M$ whose image under reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is trivial lies in $H$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $p$ a nonunit of $A$, whose residue field $\kappa$ is of characteristic $p$ and algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, the compositum of $\overline{\mathbb{Q}}$ with the function field of $X_H(M)$ inside the Laurent series field $\overline{\mathbb{Q}}((q))$, and $F_{M/p}$ for the analogous field at level $M/p$ with group `infSubgroup p M H hpM`, the image of $H$ under reduction. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$, let `Psp` be a specialisation datum `JHPlaceSpecialization p M H hpM A`, and let `Rpd` be a prolongation datum for `Psp` and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with values in the reduction $\bar{F}$, i.e. valuation subrings with surjective residue maps onto $\bar F$ whose kernels are the maximal ideals and which are compatible with $A \to \kappa$, subject in addition to compatibility of $R_1$ with coefficientwise reduction of $q$-expansions and to $f \in R_2 \iff \theta f \in R_1$ with matching residues. Let $\alpha : F_{M/p} \to F_M$ be a $\overline{\mathbb{Q}}$-algebra map which is the identity on the underlying Laurent series, and let $x \in F_M$ have $q$-expansion `jqModC`, the modular invariant $j$ as a Laurent series. The conclusion has three parts: (i) for $c \in \overline{\mathbb{Q}}$, the image of $c$ in $F_M$ lies in the integers of $R_1$ exactly when $c \in A$; (ii) for every polynomial $Q$ over $A$ whose reduction modulo the maximal ideal of $A$ is nonzero, both $Q(x)$, formed from $Q$ with coefficients pushed into $\overline{\mathbb{Q}}$, and its inverse lie in the integers of $R_1$; and (iii) every $g$ in the integers of $R_1$ is congruent modulo the maximal ideal to $\alpha u$ for some $u \in F_{M/p}$ with $\alpha u$ integral, the congruence being stated as $v(g - \alpha u) < 1$ for the valuation of $R_1$.
--
--   This identifies the first prolongation $R_1$ of a prolongation datum at a place over $p$ with $p \parallel M$ as the Gauss prolongation at the cusp: it is unramified over $A$ in the sense that its intersection with $\overline{\mathbb{Q}}$ is $A$ and the $j$-invariant has integral, transcendental reduction, while every residue is realised by a function of level $M/p$ pulled back along $\alpha$ (level lowering modulo $p$). It is used in the analysis of the reduction of $X_H(M)$ at $p$, in the construction of integral elements whose residue is a prescribed Frobenius-twisted $q$-expansion and in the description of the valuation subrings attached to such residues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :

    ((∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c ∈ Rpd.R₁.integers ↔ c ∈ A) ∧
        (∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
          Polynomial.aeval x (Q.map A.subtype) ∈ Rpd.R₁.integers ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ Rpd.R₁.integers)) ∧

    (∀ g : ↥(xHFunctionFieldBar M H), g ∈ Rpd.R₁.integers → ∃ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (α u : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers ∧ Rpd.R₁.integers.valuation (g - α u) < 1) := by sorry
