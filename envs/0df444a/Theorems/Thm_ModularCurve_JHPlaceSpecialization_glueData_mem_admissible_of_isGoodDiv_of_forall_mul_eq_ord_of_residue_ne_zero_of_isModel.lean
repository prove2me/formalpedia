-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_glueData_mem_admissible_of_isGoodDiv_of_forall_mul_eq_ord_of_residue_ne_zero_of_isModel
-- name    : ModularCurve.JHPlaceSpecialization.glueData_mem_admissible_of_isGoodDiv_of_forall_mul_eq_ord_of_residue_ne_zero_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/512c3b55-9aeb-57d5-a7ce-c51af7d0c967
-- title:
--   Good divisors with a common unit n-th root give admissible gluing data
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ in $(\mathbb{Z}/(M/p))^\times$. Let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p \in A$ a non-unit, whose residue field $\kappa$ is algebraically closed of characteristic $p$. Write $F_M =$ `xHFunctionFieldBar M H` and $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the base changes to $\overline{\mathbb{Q}}$ of the function fields of level $M$ and of level $M/p$ with the image subgroup, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`. The data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$; a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$; the map $\delta$ on places of $\bar F$ given by the action of the semilinear automorphism attached to the diamond operator `diamondActionModL` at $pb$; a finset $SS$ of pairs of places of $\bar F$ whose members are exactly the pairs $(\mathrm{Frob}(v), v)$ with $v$ supersingular, in the sense of `ssNodePairsQExp`; a place specialisation $Psp$ of type `JHPlaceSpecialization p M H hpM A`; and a prolongation datum $Rpd = (R_1, R_2)$ for $Psp$ and $\theta$, consisting of two regular prolongations of $A$ to $F_M$ with values in $\bar F$, the second obtained from the first by $\theta$. Assumed are: the type dichotomy `TypeDichotomy`, asserting for every place $W$ of $F_M$ that either $\mathrm{red}_1(W) = \mathrm{Frob}(\mathrm{red}_2(W))$ or $\delta(\mathrm{Frob}(\mathrm{red}_1(W))) = \mathrm{red}_2(W)$, where $\mathrm{red}_1 = Psp.\mathrm{reduceFst}\,\alpha$ and $\mathrm{red}_2 = Psp.\mathrm{reduceSnd}\,\beta\,\delta$; the model property `IsModel`, i.e. the two divisor laws and the two cusp laws; the order law at $\delta$-fixed affine places; the regularity law at $SS$; and cusp coverage: every place of $\bar F$ that is not an affine place is $\mathrm{red}_1(c)$ for some $\infty$-side place $c$ of $F_M$. Finally let $n > 0$, let $D$ be a degree-zero divisor on $F_M$ each of whose support places is strict of the first or of the second kind (`IsGoodDiv`), and let $f \in F_M$ lie in the integers of both $R_1$ and $R_2$ with non-zero residue for each, and satisfy $n \cdot D(W) = \mathrm{ord}_W(f)$ for all $W$. Then the gluing datum of $D$, namely the pair of push-forwards $\mathrm{red}_{1*}$ of the strict-first part and $\mathrm{red}_{2*}$ of the strict-second part of $D$ together with the trivial unit component, is admissible: both divisors have degree zero, the first vanishes at $s_1$ and the second at $s_2$ for every $s = (s_1,s_2) \in SS$.
--
--   This is the bidegree bookkeeping step in the analysis of $J_H(M)$ at a prime exactly dividing the level: a divisor class representative supported on the strict (non-node) places of the two components of the reduced fibre, admitting an $n$-th root function that is a unit with non-zero residue at both Gauss points, has gluing datum of bidegree $(0,0)$ and vanishing multiplicities at the supersingular node pairs, which is precisely the condition for it to lie in the admissible subgroup entering the glued Picard group. It is used in the construction of the de Rham model at $p$, through [`ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_glueData_mem_admissible_of_isGoodDiv_of_forall_mul_eq_ord_of_residue_ne_zero_of_isModel.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.glueData_mem_admissible_of_isGoodDiv_of_forall_mul_eq_ord_of_residue_ne_zero_of_isModel
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS)

    (hcusp₁ : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) w →
        ∃ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) c ∧ Psp.reduceFst α hα c = w)

    (n : ℕ) (hn : 0 < n)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hD : Psp.IsGoodDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
    (f : ↥(xHFunctionFieldBar M H))
    (h₁ : f ∈ Rpd.R₁.integers) (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (h₂ : f ∈ Rpd.R₂.integers) (hr₂ : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (hf : ∀ W, (n : ℤ) * (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) W = W.ord f) :
    Psp.glueData α β hα hβ δ SS (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS := by sorry
