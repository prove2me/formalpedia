-- Prove2me | Theorems.Thm_ModularCurve_atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul
-- name    : ModularCurve.atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/6634729f-16fc-5863-a34b-f16ce63a5945
-- title:
--   Atkin–Lehner slash at p conjugates diamonds on Γ₁(Mp)
-- statement:
--   Let $p$ be a prime and $M \ge 1$ an integer with $p \nmid M$, let $k \in \mathbb{Z}$, and let $f$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_1(Mp)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$ and satisfy $p \mid \gamma_{11}$ (the lower-right entry). Let $d, d'$ be natural numbers, each coprime to $Mp$, with $d' \equiv d \pmod M$ and $d'd \equiv 1 \pmod p$, and let $\delta, \delta' \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(Mp)$ with upper-left entries reducing to $d$, respectively $d'$, modulo $Mp$. Write $P := \mathrm{heckeDiagMatrix}\, p$ for the element of $\mathrm{GL}_2(\mathbb{R})$ given by the upper-triangular matrix $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$, acting on the upper half-plane by $\tau \mapsto p\tau$. Then, as functions on the upper half-plane, $$\tau \mapsto \bigl((f\mid_k \delta)\mid_k \gamma\bigr)(P\cdot\tau) \quad\text{equals}\quad \Bigl(\tau \mapsto (f\mid_k \gamma)(P\cdot\tau)\Bigr)\Big|_k \delta',$$ where $\mid_k$ is the weight-$k$ slash action.
--
--   Writing $Wh := \bigl(\tau \mapsto (h\mid_k\gamma)(p\tau)\bigr)$ for the partial Atkin–Lehner slash at $p$ attached to such a $\gamma$, the identity says $W(f\mid_k\delta) = (Wf)\mid_k\delta'$: the operator $W$ intertwines the diamond operator $\langle d\rangle$ on $\Gamma_1(Mp)$ with $\langle d'\rangle$, where $d'$ agrees with $d$ modulo $M$ and is inverse to $d$ modulo $p$. It is a function-level statement, with no reference to $q$-expansions or coefficient fields, and it is used in the comparison of diamond operators under the Atkin–Lehner automorphism of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (d d' : ℕ) (hd : d.Coprime (M * p)) (hd' : d'.Coprime (M * p))
    (hdM : (d' : ZMod M) = (d : ZMod M)) (hdp : (d' : ZMod p) * (d : ZMod p) = 1)
    (δ δ' : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p)) (hδ' : δ' ∈ CongruenceSubgroup.Gamma0 (M * p))
    (hδ00 : ((δ 0 0 : ℤ) : ZMod (M * p)) = (d : ZMod (M * p)))
    (hδ'00 : ((δ' 0 0 : ℤ) : ZMod (M * p)) = (d' : ZMod (M * p))) :
    (fun τ : UpperHalfPlane => (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) =
      ((fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∣[k] δ') := by sorry
