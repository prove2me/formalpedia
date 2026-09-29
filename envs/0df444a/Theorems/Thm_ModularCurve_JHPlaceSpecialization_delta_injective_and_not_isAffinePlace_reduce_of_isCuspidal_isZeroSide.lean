-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide
-- name    : ModularCurve.JHPlaceSpecialization.delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/5ef77251-64c1-5064-9bb6-5749bbc32ff3
-- title:
--   δ injective; cuspidal places reduce to non-affine places
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H`, $F_{M/p} =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` and $\bar F$ for the mod-$p$ $q$-expansion function field `JHNeronObjectAtP.Fbar p M H hpM κ`. Given a $\overline{\mathbb{Q}}$-automorphism $\theta$ of $F_M$, integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$, a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$, and a self-map $\delta$ of the places of $\bar F$ over $\kappa$ acting as the semilinear automorphism attached to the diamond operator `diamondActionModL` at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); further a finite set $SS$ of pairs of places whose members are exactly the supersingular node pairs `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p` (pairs $(v_1,v_2)$ with $v_2$ supersingular and $v_1$ its Frobenius image); a specialization datum $Psp$, a prolongation datum $Rpd$ for $\theta$; the type dichotomy for $(\alpha,\beta,\delta)$, asserting for each place $W$ of $F_M$ that $r_1(W) := Psp.\mathrm{sp}(W|_\alpha)$ is the Frobenius image of $r_2(W) := \delta(Psp.\mathrm{sp}(W|_\beta))$ or else $\delta$ of the Frobenius image of $r_1(W)$ is $r_2(W)$; finiteness of the set of $\delta$-fixed places; the model laws for $Rpd$ (the two divisor laws and the two cusp laws); the $q$-expansion laws $\alpha u = u$ and $\beta u =$ `qExpand` $_p(u)$ on Laurent series; and the hypothesis that every place $w$ of $\bar F$ which is not affine (no element with $q$-expansion $j(q)$ takes a value in $\kappa$ at $w$) is simultaneously $r_1$ of some $\infty$-side place and $r_2$ of some $0$-side place. Then $\delta$ is injective; if $C$ is a place of $F_M$ at which $j$ takes no $A$-integral value (for every $x$ with $q$-expansion $j(q)$ and every $a \in A$, $\mathrm{ord}_C(x - a) \le 0$) then $r_1(C)$ is not affine; if $C$ satisfies the same condition with $j(q)$ replaced by $j(q^p)$ then $r_2(C)$ is not affine; and if $C$ lies on the $0$-side of the cuspidal region (that condition for $j(q^p)$, together with elements $x, x'$ with $q$-expansions $j(q)$, $j(q^p)$ and some $\tau \in A$ of residue $1$ with $C$-value $\tau$ at $x/x'^{\,p}$) then $r_1(C)$ is not affine.
--
--   This is a reading lemma for the place-specialization kit of $X_H(M)$ at a prime $p$ exactly dividing $M$: it records that the diamond-twisted second reading $\delta$ is injective on places of the mod-$p$ fibre and that cuspidality upstairs forces the two reductions to land away from the affine locus, on each of the two sheets. It is cited by the common-unit constructions for the prolongation datum, which produce functions with prescribed poles along the reductions $r_1$ and $r_2$ in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide
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
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
    (hmodel : Rpd.IsModel α β hα hβ δ)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w)) :
    Function.Injective δ ∧
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) C → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα C)) ∧
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) C → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceSnd β hβ δ C)) ∧
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα C)) := by sorry
