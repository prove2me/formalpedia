-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/a40a169a-eb09-5dde-8fa0-7315c93b3ca7
-- title:
--   Cusp chart at infinity: integrality and regularity over a cusp
-- statement:
--   Fix natural numbers $p$ (prime) and $M\neq 0$ with $p\mid M$ but $p^2\nmid M$, and $M/p\neq 0$, and a subgroup $H\le(\mathbb{Z}/M)^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that the image of $p$ lies in the nonunits of $A$, with residue field $\kappa$ of characteristic $p$ and algebraically closed. Write $F_M=$ `xHFunctionFieldBar M H` and $F_{M/p}=$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, intermediate fields of $\overline{\mathbb{Q}}\subseteq\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$, and $\bar F=$ `JHNeronObjectAtP.Fbar p M H hpM κ`. Let $\theta$ be a $\overline{\mathbb{Q}}$-automorphism of $F_M$, and $\alpha:F_{M/p}\to F_M$ a $\overline{\mathbb{Q}}$-algebra map which is the identity on underlying Laurent series and is integral. Let `Psp` be a `JHPlaceSpecialization` for these data (a specialization map `sp` from places of $F_{M/p}$ to places of $\bar F$ over $\kappa$, surjective, compatible with divisors of functions and with $\mathrm{Pic}^0$, and equivariant for inertia and Frobenius at $p$), and `Rpd` a `ProlongationDatum` for `Psp` and $\theta$, consisting of regular prolongations $R_1,R_2$ of $A$ from $F_M$ to $\bar F$ whose residues compute coefficientwise reduction of Laurent series and with $R_2$ obtained from $R_1$ by precomposition with $\theta$. Let $x'\in F_{M/p}$ have Laurent series $j(q)$ (`jqModC`) and $t\in F_M$ have Laurent series $j(q^p)\,j(q)^{-p}$. Let $v$ be a place of $\bar F$ over $\kappa$ which is not affine, i.e. there is no $x\in\bar F$ with Laurent series $j(q)$ and no $a\in\kappa$ with $v$-value $a$ at $x$, and assume every place $W$ of $F_M$ with `Psp.reduceFst α hα W`$=v$ (that is, $\mathrm{sp}$ of the restriction of $W$ along $\alpha$ equals $v$) is cuspidal: $\mathrm{ord}_W(x-a)\le 0$ for all $x\in F_M$ with Laurent series $j(q)$ and all $a\in A$. Then for every $s$ in `cuspChartSetInf A α x' t`, the union of the $\alpha$-image of `integralOverPoleChart A x'` with the set of elements $t-a$ for $a\in A$, one has $s\in R_1$, the $R_1$-residue of $s$ lies in the valuation subring of $v$, and $s$ lies in the valuation subring of every place $W$ of $F_M$ with `Psp.reduceFst α hα W`$=v$.
--
--   This is the verification, at a cusp of the fibre at $p$, of the three pointwise conditions (integrality for the first prolongation, regularity of the residue at $v$, and regularity at all places of $F_M$ lying over $v$) required of a chart set near the component at infinity of the Deligne–Rapoport model of $X_H(M)$ at $p$. It is used in the construction of cuspidal charts at infinity and in the associated multiplicativity statement for elements of the chart set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHCuspChartSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p)
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hvna : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) v)
    (hcuspv : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = v →
      (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) W)
    (s : ↥(xHFunctionFieldBar M H)) (hs : s ∈ (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t)) :
    ∃ h₁ : s ∈ Rpd.R₁.integers,
      (Rpd.R₁.residue ⟨s, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ v.toValuationSubring ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = v → s ∈ W.toValuationSubring := by sorry
