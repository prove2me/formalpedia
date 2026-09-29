-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_dualWhittaker_eq_dualWhittakerFn3
-- name    : LanglandsTunnell.CubicInduction.CubicInductionForm.dualWhittaker_eq_dualWhittakerFn3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/422fbbce-7c8e-596d-87d8-4ff4acbe8ad2
-- title:
--   Dual Whittaker function as reflected Whittaker function
-- statement:
--   Let $K$ be a number field, equipped with an algebra structure of $\mathcal{O}_{\mathbb Q}$ on $\mathcal{O}_K$ that is integral, let $\psi$ be an additive character of the adele ring of $\mathbb Q$ with values in $\mathbb C$, and let $\mu$ be a character of the idele group of $K$ with values in $\mathbb C^\times$. Let $D$ be a subset of $\mathrm{GL}_2$ of the adeles of $\mathbb Q$, let $U$ assign to each ideal of $\mathcal{O}_{\mathbb Q}$ a subgroup of that adelic $\mathrm{GL}_2$, and let $\mathrm{gen}$ assign an element of it to each finite place. Let $F$ be a `CubicInductionForm` for $K$, $\psi$ and $\mu$ over the carrier pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, i.e. over the pins whose measurable structures are the Borel ones on adelic $\mathrm{GL}_2$ and on the adeles, whose measures are the adelic Haar measure on $\mathrm{GL}_2$ and the adelic additive Haar measure conditioned on the adelic box (the product of the infinite box with the integral finite adeles), whose central subgroup is all of the idele group, and whose $D$, $U$ and $\mathrm{gen}$ are the data given. Then the field `F.dualWhittaker` equals `dualWhittakerFn3 F.whittaker`, that is, for every $g$ in $\mathrm{GL}_3$ of the adeles of $\mathbb Q$ one has $F.\mathrm{dualWhittaker}(g) = F.\mathrm{whittaker}(w_3 \cdot \mathrm{transposeInv3}(g))$, where $w_3 =$ `longWeyl3` is the antidiagonal permutation matrix $!![0,0,1;0,1,0;1,0,0]$ of $\mathrm{GL}_3$ and `transposeInv3` is the map of that name on $\mathrm{GL}_3$.
--
--   This records, for cubic induction data, the standard relation between the Whittaker function of a form and that of its contragredient, $\widetilde W(g) = W(w_3\,{}^t g^{-1})$, in the form used by Jacquet, Piatetski-Shapiro and Shalika in their treatment of Rankin–Selberg convolutions. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, where the dual Whittaker function enters the local and global zeta integrals and the functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_dualWhittaker_eq_dualWhittakerFn3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.CubicInductionForm.dualWhittaker_eq_dualWhittakerFn3
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (F : CubicInductionForm K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ)
    (_hcont : Continuous F.form) :
    F.dualWhittaker = dualWhittakerFn3 F.whittaker := by sorry
