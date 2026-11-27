-- Prove2me | Theorems.Thm_MohP3_Palomar_formalLocal_setTheoretic_completeIntersection
-- name    : MohP3.Palomar.formalLocal_setTheoretic_completeIntersection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:45:19.696007+00:00
-- url     : https://prove2.me/theorems/d8799fc8-6b3f-5336-9a7c-e22f84396bde
-- title:
--   Palomar: formal Local set Theoretic complete Intersection
-- statement:
--   The Palomar construction uses the formal Local set Theoretic complete Intersection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/Solution.lean#L46-L81
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/Solution.lean#L46-L81

module
public import Definitions.Def_MohP3
public import Definitions.Def_MohP3_Solution
public import Theorems.Thm_MohP3_FormalLocal_chiS_X0
public import Theorems.Thm_MohP3_FormalLocal_chiS_X1
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_wt_dd
public import Theorems.Thm_MohP3_iotaK_C
public import Theorems.Thm_MohP3_iotaK_X
public import Theorems.Thm_MohP3_iota_C
public import Theorems.Thm_MohP3_iota_X
public import Theorems.Thm_MohP3_iota_ofNat
public import Theorems.Thm_MohP3_rho_C
public import Theorems.Thm_MohP3_rho_k_C
public import Theorems.Thm_MohP3_rho_k_xk
public import Theorems.Thm_MohP3_rho_k_yk
public import Theorems.Thm_MohP3_rho_k_zk
public import Theorems.Thm_MohP3_rho_x
public import Theorems.Thm_MohP3_rho_y
public import Theorems.Thm_MohP3_rho_z
public import Theorems.Thm_MohP3_sigmaK_xk
public import Theorems.Thm_MohP3_sigmaK_yk
public import Theorems.Thm_MohP3_sigmaK_zk
public import Theorems.Thm_MohP3_sigma_x
public import Theorems.Thm_MohP3_sigma_y
public import Theorems.Thm_MohP3_sigma_z
attribute [local simp] MohP3.FormalLocal.chiS_X0
attribute [local simp] MohP3.FormalLocal.chiS_X1
attribute [local simp] MohP3.HilbertBurch.rowMap_apply
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.wt_dd
attribute [local simp] MohP3.iotaK_C
attribute [local simp] MohP3.iotaK_X
attribute [local simp] MohP3.iota_C
attribute [local simp] MohP3.iota_X
attribute [local simp] MohP3.iota_ofNat
attribute [local simp] MohP3.rho_C
attribute [local simp] MohP3.rho_k_C
attribute [local simp] MohP3.rho_k_xk
attribute [local simp] MohP3.rho_k_yk
attribute [local simp] MohP3.rho_k_zk
attribute [local simp] MohP3.rho_x
attribute [local simp] MohP3.rho_y
attribute [local simp] MohP3.rho_z
attribute [local simp] MohP3.sigmaK_xk
attribute [local simp] MohP3.sigmaK_yk
attribute [local simp] MohP3.sigmaK_zk
attribute [local simp] MohP3.sigma_x
attribute [local simp] MohP3.sigma_y
attribute [local simp] MohP3.sigma_z


set_option autoImplicit true
@[expose] public section
public section
open MohP3 MohP3.Palomar

theorem MohP3.Palomar.formalLocal_setTheoretic_completeIntersection
    (k : Type*) [Field k] [CharZero k] :
    let R := MvPowerSeries (Fin 3) k
    let x : R := MvPowerSeries.X 0
    let y : R := MvPowerSeries.X 1
    let z : R := MvPowerSeries.X 2
    let f1 := x^4 - x^2*y^4*z^3 - 2*x*y^6*z^2 - 4*x*y*z - 3*y^3*z^5 + 3*y^3
    let f2 := x^3*y - x*y^5*z^3 - 3*x*z^2 - 2*y^7*z^2 + 2*y^2*z
    let f3 := 2*x^3*z - 3*x^2*y^2 - 2*x*y^4*z^4 - y^6*z^3 + y*z^2
    let f4 := x^2*y*z - 2*x*y^3 - y^5*z^4 + z^3
    let ell := 64*x^4*y*z^2 - 40*x^3*y^3*z + 72*x*y^2*z^3 - 81*y^4*z^2
    let kappa := -40*x^3*y^2*z^2 + 25*x^2*y^4*z + 36*y^3*z^3
    let H1 := 81*f4 - 24*x*f1 + ell*f3
    let H2 := -12*y*f1 + 27*x*f2 + kappa*f3
    let P : Ideal R := Ideal.span ({f1, f2, f3, f4} : Set R)
    let Q : Ideal R := Ideal.span ({H1, H2} : Set R)
    let aa : Fin 3 → PowerSeries k :=
      ![PowerSeries.X^6 + PowerSeries.X^31, PowerSeries.X^8, PowerSeries.X^10]
    let haa : MvPowerSeries.HasSubst aa := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro i
      have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
        PowerSeries.constantCoeff_X
      fin_cases i <;> simp [aa, hX]
    let psi : R →ₐ[k] PowerSeries k := MvPowerSeries.substAlgHom haa
    RingHom.ker psi = P ∧
    Q.radical = P ∧
    P.height = 2 ∧
    (⨅ s ∈ {s : Finset R | (Ideal.span (s : Set R)).radical = P.radical},
      (s.card : ℕ∞)) = 2 := by sorry
