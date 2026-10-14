-- Prove2me | Theorems.Thm_NoHair_KNE_thm_maxwell
-- name    : NoHair.KNE.thm_maxwell
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-13T08:33:05.18499+00:00
-- url     : https://prove2.me/theorems/a193ccd8-906e-420e-9057-670b9556dc7e
-- title:
--   Kerr–Newman Maxwell source in closed form
-- statement:
--   Polynomial identities in the atoms: if $k_1^2+k_2^2+k_3^2=1$ and $W(r^2+a^2k_3^2)=1$, then (i) the field strength `FS` of $A=H k$ (with $H=erW$) equals the closed form `FA`, (ii) raising both indices with $g^{-1}=\eta-f\,k^\sharp k^{\sharp T}$ gives `FupA`, (iii) the invariant $F_{\alpha\beta}F^{\alpha\beta}$ equals `FFA`, and (iv) the Maxwell source tensor `TS` equals the closed-form Ricci tensor `RicA` (all in block `NoHair_KerrNewmanEinstein_Base`).
--
--   This is an intermediate step in the machine-checked proof of `NoHair.kerrNewman_einstein` (Kerr–Newman satisfies the Einstein equation in Kerr–Schild coordinates). Its proof uses the definition blocks `NoHair_KerrNewmanEinstein_MaxwellF`, `NoHair_KerrNewmanEinstein_MaxwellT`.
-- source:
--   Original formalization for the Prove2Me mission *No-Hair Conjecture: Uniqueness of Stationary Kerr–Newman Black Holes*; Kerr–Newman metric: E. T. Newman et al., J. Math. Phys. 6 (1965) 918, https://doi.org/10.1063/1.1704351.

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem thm_maxwell (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    (∀ μ ν, FS a e R K1 K2 K3 W μ ν = FA a e R K1 K2 K3 W μ ν) ∧
    (∀ α β, ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W α μ * ginvA a m e R K1 K2 K3 W β ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W α β) ∧
    (∑ α, ∑ β, FA a e R K1 K2 K3 W α β * FupA a m e R K1 K2 K3 W α β = FFA a m e R K1 K2 K3 W) ∧
    (∀ μ ν, TS a m e R K1 K2 K3 W μ ν = RicA a m e R K1 K2 K3 W μ ν) := by
  sorry

end NoHair.KNE
