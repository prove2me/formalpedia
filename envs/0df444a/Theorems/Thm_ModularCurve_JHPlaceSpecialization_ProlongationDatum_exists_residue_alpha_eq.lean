-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_residue_alpha_eq
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_residue_alpha_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/9e3dfcaf-6d32-5ae8-a0cc-ccebf55380db
-- title:
--   Level-M/p functions fill the first residue field
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, whose residue field $\kappa = \mathrm{ResidueField}\,A$ is of characteristic $p$ and algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, the compositum inside $\overline{\mathbb{Q}}((q))$ of $\overline{\mathbb{Q}}$ with the function field of $X_H(M)$, and $F_{M/p}$ for the analogous field at level $M/p$ with the group `infSubgroup p M H hpM`, the image of $H$ under $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$; write $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the subfield $\mathrm{qExpFunctionFieldC}\,\kappa\,(\Gamma_N(p,M,H))$ of $\kappa((q))$. Given a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$, a $\overline{\mathbb{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$ that preserves the underlying Laurent series of every element, a specialization datum $P_{\mathrm{sp}}$ of type `JHPlaceSpecialization p M H hpM A` (a map $\mathrm{sp}$ on places of $F_{M/p}$ to places of $\bar F$ over $\kappa$, together with a map on degree-zero divisor classes and the stated compatibilities with orders of functions, $q$-expansions, inertia and Frobenius), and a prolongation datum $R_{\mathrm{pd}}$ over $P_{\mathrm{sp}}$ and $\theta$ — consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue field $\bar F$, the prescribed reduction law on $A$-integral $q$-expansions for $R_1$, and $R_2$ obtained from $R_1$ by transport along $\theta$ — the conclusion is: every $a \in \bar F$ is of the form $a = R_1.\mathrm{residue}(\alpha v)$ for some $v \in F_{M/p}$ with $\alpha v$ in the valuation subring $R_1.\mathrm{integers}$.
--
--   Equivalently, the valuation ring $\alpha^{-1}(R_1.\mathrm{integers})$ of $F_{M/p}$ has residue field all of $\bar F$, i.e. residue degree one for the first of the two prolongations; this is the surjectivity half of the two-residue comparison at level $M$ versus $M/p$. It is used by [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one) and [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.not_integers_le_integers_and_not_integers_le_integers`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.not_integers_le_integers_and_not_integers_le_integers), which separate the two prolongations, and by the order and Frobenius computation [`ModularCurve.XHDRModelAtP.exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_residue_alpha_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_residue_alpha_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    ∀ a : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), ∃ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h : α v ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨α v, h⟩ = a := by sorry
