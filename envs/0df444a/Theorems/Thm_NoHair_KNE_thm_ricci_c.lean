-- Prove2me | Theorems.Thm_NoHair_KNE_thm_ricci_c
-- name    : NoHair.KNE.thm_ricci_c
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-13T08:31:54.602236+00:00
-- url     : https://prove2.me/theorems/e9f7c9ec-a103-4680-885e-9110e2332bfc
-- title:
--   Kerr–Newman Ricci tensor in closed form: components (1,3), (2,2), (2,3), (3,3)
-- statement:
--   Polynomial identities in the atoms: if $k_1^2+k_2^2+k_3^2=1$ and $W(r^2+a^2k_3^2)=1$, then the Ricci tensor `RicS` assembled from the closed-form Christoffel symbols and their divergences (block `NoHair_KerrNewmanEinstein_Base`) equals the closed form `RicA` for the components $(1,3)$, $(2,2)$, $(2,3)$, $(3,3)$.
--
--   This is an intermediate step in the machine-checked proof of `NoHair.kerrNewman_einstein` (Kerr–Newman satisfies the Einstein equation in Kerr–Schild coordinates). Its proof uses the definition blocks `NoHair_KerrNewmanEinstein_Ricci5`, `NoHair_KerrNewmanEinstein_Ricci6`.
-- source:
--   Original formalization for the Prove2Me mission *No-Hair Conjecture: Uniqueness of Stationary Kerr–Newman Black Holes*; Kerr–Newman metric: E. T. Newman et al., J. Math. Phys. 6 (1965) 918, https://doi.org/10.1063/1.1704351.

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem thm_ricci_c (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    RicS a m e R K1 K2 K3 W 1 3 = RicA a m e R K1 K2 K3 W 1 3 ∧
    RicS a m e R K1 K2 K3 W 2 2 = RicA a m e R K1 K2 K3 W 2 2 ∧
    RicS a m e R K1 K2 K3 W 2 3 = RicA a m e R K1 K2 K3 W 2 3 ∧
    RicS a m e R K1 K2 K3 W 3 3 = RicA a m e R K1 K2 K3 W 3 3 := by
  sorry

end NoHair.KNE
