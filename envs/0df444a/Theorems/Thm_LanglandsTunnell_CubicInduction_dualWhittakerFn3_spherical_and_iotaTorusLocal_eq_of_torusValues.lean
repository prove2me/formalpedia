-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues
-- name    : LanglandsTunnell.CubicInduction.dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/c71f8a68-6027-5f1e-af16-fe24e6648bff
-- title:
--   Contragredient of a spherical GL₃ Whittaker function
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), let $\psi_v$ be an additive character of the completion $\mathbb{Q}_v$ with values in $\mathbb{C}$, and let $W$ be a complex-valued function on $\mathrm{GL}_3(\mathbb{Q}_v)$. Assume: $W$ is right invariant under `localMaximalCompact3`, the subgroup of those $k$ all of whose entries and all of whose entries of $k^{-1}$ have valuation $\le 1$, i.e. $W(gk)=W(g)$; $W$ satisfies $W(\mathrm{u}(x,y,z)\,g)=\psi_v(x+y)W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $\mathrm{u}(x,y,z)$ is the upper unipotent matrix with superdiagonal entries $x,y$ and corner entry $z$; for complex numbers $e_1,e_2,e_3$ with $e_3\ne 0$, $W(\varpi\cdot 1_3\cdot g)=e_3W(g)$, where $\varpi\cdot 1_3$ is `centralGen v`, the scalar matrix with the uniformiser unit at $v$ on the diagonal; $W(1)=1$; and, writing $N=$ `cNormQ v` for the absolute norm of $v$ and $s_n=$ `sphericalTorusValue e₁ e₂ e₃ n` for the sequence with $s_0=1$, $s_1=e_1$, $s_2=e_1^2-e_2$, $s_{n+3}=e_1s_{n+2}-e_2s_{n+1}+e_3s_n$, the torus values $W(\mathrm{iotaTorusLocal}\,v\,n)=N^{-n}s_n$ for all $n$ and $W(\mathrm{twoRowPointLocal}\,v\,k_1\,(k_2+1))=N^{-k_1}(s_{k_1}s_{k_2+1}-s_{k_1+1}s_{k_2})$ whenever $k_2+1\le k_1$; here `iotaTorusLocal v n` is the image under the upper-left block embedding `iotaGL` of `diagHom` applied to the $n$-th power of the unit `ratPrimeUnit v`, and `twoRowPointLocal v k₁ k₂` the image of the diagonal $\mathrm{GL}_2$ element `diagUnits2` at the $k_1$-st and $k_2$-nd powers of that unit. Then the dual function $\widetilde W(g)=W(w_3\,{}^t g^{-1})$, with $w_3$ the long Weyl element `longWeyl3`, is again right invariant under `localMaximalCompact3`, satisfies the Whittaker transformation law for $\psi_v^{-1}$, has $\widetilde W(1)=1$, satisfies $\widetilde W(\varpi\cdot 1_3\cdot g)=e_3^{-1}\widetilde W(g)$, and for every $n$ has one-row torus value $\widetilde W(\mathrm{iotaTorusLocal}\,v\,n)=N^{-n}\,s_n(e_2e_3^{-1},e_1e_3^{-1},e_3^{-1})$.
--
--   This is the passage from a class-one Whittaker function on $\mathrm{GL}_3(\mathbb{Q}_v)$ to its contragredient, which is spherical with the inverted Satake parameters $(e_2/e_3,\,e_1/e_3,\,1/e_3)$; the two-row torus values of $W$ are what convert into the one-row values of $\widetilde W$, by way of `twoRowTable_contragredient_eq_inv_pow_mul`. It feeds the Euler product for the local $3\times 1$ zeta integral of the dual function, `hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le`, used in the functional equation required by the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  NumberField.InfinitePlace LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    (hK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (e₁ e₂ e₃ : ℂ) (he₃ : e₃ ≠ 0)
    (hcen : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (h1 : W 1 = 1)
    (htv₁ : ∀ n : ℕ, W (iotaTorusLocal v n) = (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n)
    (htv₂ : ∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
      (cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂)) :
    IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (dualWhittakerFn3 W) ∧
    IsGL3PsiWhittakerFn ψv⁻¹ (dualWhittakerFn3 W) ∧
    dualWhittakerFn3 W 1 = 1 ∧
    (∀ g : LocalGL3 v, dualWhittakerFn3 W (centralGen v * g) = e₃⁻¹ * dualWhittakerFn3 W g) ∧
    (∀ n : ℕ, dualWhittakerFn3 W (iotaTorusLocal v n) =
      (cNormQ v)⁻¹ ^ n * sphericalTorusValue (e₂ * e₃⁻¹) (e₁ * e₃⁻¹) e₃⁻¹ n) := by sorry
