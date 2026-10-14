-- Prove2me | Theorems.Thm_NoHair_KNE_thm_christoffel
-- name    : NoHair.KNE.thm_christoffel
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-13T08:21:40.108074+00:00
-- url     : https://prove2.me/theorems/8dcd053d-2b42-4da1-b938-e3b583380372
-- title:
--   Kerr–Newman Christoffel symbols in closed form
-- statement:
--   For all real $m,a,e$ and every point $z$ of coordinate space with Kerr–Schild radius $r(z)>0$, the Christoffel symbols $\Gamma^i_{jk}$ of the Kerr–Newman metric (`christoffel (kerrNewmanMetric m a e) z i j k`) equal the explicit polynomial `Gam` in the atoms $r$, $k_1,k_2,k_3$ (components of the Kerr–Schild null covector) and $W=1/(r^2+a^2k_3^2)$, as defined in the block `NoHair_KerrNewmanEinstein_Base`.
--
--   This is an intermediate step in the machine-checked proof of `NoHair.kerrNewman_einstein` (Kerr–Newman satisfies the Einstein equation in Kerr–Schild coordinates). Its proof uses the definition blocks `NoHair_KerrNewmanEinstein_Christoffel`.
-- source:
--   Original formalization for the Prove2Me mission *No-Hair Conjecture: Uniqueness of Stationary Kerr–Newman Black Holes*; Kerr–Newman metric: E. T. Newman et al., J. Math. Phys. 6 (1965) 918, https://doi.org/10.1063/1.1704351.

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem thm_christoffel (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i j k : Fin 4) :
    christoffel (kerrNewmanMetric m a e) z i j k = Gam a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) i j k := by
  sorry

end NoHair.KNE
