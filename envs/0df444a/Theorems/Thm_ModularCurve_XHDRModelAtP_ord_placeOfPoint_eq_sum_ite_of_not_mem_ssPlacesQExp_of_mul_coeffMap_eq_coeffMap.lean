-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
-- name    : ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/97c1b39b-6830-59aa-b775-d3281a78334f
-- title:
--   Order of the reduced function at non-supersingular places
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbf{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbf{Z}/M)^\times \to (\mathbf{Z}/(M/p))^\times$ is trivial. Let $Pl$ be a valuation subring of $\overline{\mathbf{Q}}$ with $p$ a non-unit of $Pl$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, let the $q$-expansion $j$ lie in the full-level $q$-expansion function field over $\mathbf{Q}$, and let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj` together with a ring map $\rho : R\,p \to Pl$ lifting the structure map $R\,p \to \overline{\mathbf{Q}}$. Let $f$ lie in `xHFunctionFieldBar M H`, the base change to $\overline{\mathbf{Q}}$ of the function field of $X_H(M)$ inside Laurent series, and let $x,y$ be Laurent series over $Pl$ whose coefficientwise reductions $\bar x,\bar y$ to $\kappa$ are non-zero and satisfy $f \cdot y = x$ after the coefficientwise inclusion $Pl \hookrightarrow \overline{\mathbf{Q}}$; let $g$ be an element of the $q$-expansion function field over $\kappa$ at level $\Gamma_N(p,M,H)$ with $g\,\bar y = \bar x$. Assume given a finite family indexed by $\iota$ consisting of: $\overline{\mathbf{Q}}$-points $yv_j$ of the curve model $\mathfrak{X}.\mathrm{Meta}$ (sections of its structure map to $\operatorname{Spec} \overline{\mathbf{Q}}$); $Pl$-valued points $u_j$ of `X p (ΓM M H) hj` over $\operatorname{Spec}\rho$ whose restriction along $Pl \hookrightarrow \overline{\mathbf{Q}}$ is $yv_j$ transported through the isomorphism $\mathfrak{X}.\mathrm{eeta}$ followed by the first projection; $\kappa$-points $u\kappa_j$ of the fibre of the model at $\mathrm{res}\circ\rho$ (sections of the second projection) whose first projection is the reduction of $u_j$; and integers $n_j$, such that for every place $v$ of `xHFunctionFieldBar M H` over $\overline{\mathbf{Q}}$ one has $v.\mathrm{ord}\,f = \sum_j \delta_{v,\,\mathrm{pointEquivPlace}(yv_j)} n_j$, i.e. $\operatorname{div} f = \sum_j n_j [yv_j]$. Then for every closed point $\bar P$ of the curve $(\mathfrak{X}.\mathrm{Mfib}\ Pl\ hPl\ \rho\ h\rho).C$ whose associated place is not in `ssPlacesQExp κ (ΓN p M H hpM) p`, the order of $g$ at that place equals $\sum_j n_j$ taken over those $j$ for which the image of $\bar P$ under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\ 0$ coincides with the image of the closed point of $\operatorname{Spec}\kappa$ under $u\kappa_j$.
--
--   This is the local specialisation computation for the divisor of a function on $X_H(M)_{\overline{\mathbf{Q}}}$ whose $q$-expansion is a unit along the component of the special fibre at $p$ through the cusp $\infty$: the order of the reduced function $g$ at a non-supersingular place of that component counts, with multiplicities $n_j$, exactly those sections of the model that specialise to the given closed point. It supports the description of the specialisation of divisor classes on the Jacobian at $p$, used in the level-lowering step at a prime exactly dividing the level, and is cited by the companion computation over the other component and by the statement on configured representatives of divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 800000 in
open Classical in
open ModularCurve in

theorem ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (f : ↥(ModularCurve.xHFunctionFieldBar M H))
    (x y : LaurentSeries ↥Pl)
    (hxbar : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x ≠ 0)
    (hybar : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0)
    (hfxy : (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
    (hg : (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y =
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x)

    {ι : Type} [Fintype ι]
    (yv : ι → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : ι → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : ∀ j, barPt Pl ≫ (u j).1 = (yv j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : ι → (Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ)))
    (huκ₁ : ∀ j, uκ j ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ (u j).1)
    (huκ₂ : ∀ j, uκ j ≫ pullback.snd _ _ = 𝟙 _)
    (n : ι → ℤ)
    (hdiv : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      v.ord f = (∑ j, Finsupp.single (𝔛.Meta.pointEquivPlace (yv j)) (n j)) v)

    (Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
    (hPbar : (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∉
      ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p) :
    ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar).ord g =
      ∑ j, if (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1 =
              (uκ j).base (IsLocalRing.closedPoint (ResidueField ↥Pl))
           then n j else 0 := by sorry
