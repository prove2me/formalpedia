-- Prove2me | Theorems.Thm_ModPForms_heckePS_heckePS_comm
-- name    : ModPForms.heckePS_heckePS_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/616c4c1b-28f4-518e-b99a-421cdd7a12cf
-- title:
--   Commutativity of the weight-k coefficient Hecke operators
-- statement:
--   Let $F$ be a field, let $k$ be an integer, let $\ell$ and $\ell'$ be natural numbers assumed prime, and let $\varphi$ be a formal power series over $F$ in one variable. Write $T_m$ for the operator [`ModPForms.heckePS k m`](def/CuspForm_ModPForms.html#L20) on `PowerSeries F`, defined coefficientwise by: the $n$-th coefficient of $T_m\varphi$ is the $(nm)$-th coefficient of $\varphi$ plus, when $m$ divides $n$, the term $(m)^{k-1}$ — the image of $m$ in $F$ raised to the integer power $k-1$ — times the $(n/m)$-th coefficient of $\varphi$, and plus $0$ otherwise. The theorem asserts the equality of power series $T_\ell(T_{\ell'}\varphi) = T_{\ell'}(T_\ell\varphi)$. No modularity or convergence assumption enters: $\varphi$ is an arbitrary formal power series, the weight $k$ is an arbitrary integer (so that $\ell^{k-1}$ is read as a power in the multiplicative group of $F$ when $k<1$), and the characteristic of $F$ is unrestricted, in particular $\ell$ or $\ell'$ may vanish in $F$.
--
--   This is the formal-$q$-expansion form of the classical statement that the weight-$k$ Hecke operators $T_\ell$ and $T_{\ell'}$ commute, here carried out purely as an identity between coefficient recipes on `PowerSeries F`. It is used in the construction of systems of simultaneous Hecke eigenvectors, being cited by [`ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem`](thm.html#ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_heckePS_heckePS_comm.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.heckePS_heckePS_comm
    (F : Type) [Field F] (k : ℤ) (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (φ : PowerSeries F) :
    ModPForms.heckePS k ℓ (ModPForms.heckePS k ℓ' φ) = ModPForms.heckePS k ℓ' (ModPForms.heckePS k ℓ φ) := by sorry
