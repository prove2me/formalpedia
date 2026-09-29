-- Prove2me | Theorems.Thm_ModPForms_mem_modPMod_sub_of_qP_mul_mem
-- name    : ModPForms.mem_modPMod_sub_of_qP_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/cb4165f4-f487-577a-96e2-d6ca2b9fbc94
-- title:
--   Weight descent by p-1 under multiplication by P
-- statement:
--   Fix a natural number $p$ with $5 \le p$, a natural number $N'$ which is nonzero and not divisible by $p$, and a field $F$ of characteristic $p$ (so $p$ is prime). Let $k$ be an integer not divisible by $p$. For an integer $w$ write $M_w$ for the $F$-submodule of $F\langle\langle q\rangle\rangle$ spanned by those power series of the form $\sum_n \overline{a_n}q^n$ for which there exist a modular form $f$ of weight $w$ on $\Gamma_0(N')$ and integers $a_n$ with the $n$-th coefficient of the $q$-expansion of $f$ (taken with width $1$) equal to $a_n$ for all $n$; thus $M_w$ is the span of the reductions mod $p$ of $q$-expansions of integral-coefficient weight-$w$ forms on $\Gamma_0(N')$. Let $\varphi \in F\langle\langle q\rangle\rangle$ and let $\tilde P$ denote the image in $F\langle\langle q\rangle\rangle$ of $1 - 24\sum_{n \ge 1}\sigma_1(n)q^n$. The assertion is: if $\varphi \in M_k$ and $\tilde P\,\varphi \in M_{k+2}$, then $\varphi \in M_{k-(p-1)}$.
--
--   This is the filtration-lowering lemma of Katz and Swinnerton-Dyer for mod $p$ modular forms on $\Gamma_0(N')$: multiplication by the reduction of $E_2$ raises the weight by $2$ only at the cost of divisibility by the Hasse invariant, which has weight $p-1$ and $q$-expansion $1$. It is used to show that the theta operator strictly raises the filtration, via [`ModPForms.thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_of_not_dvd`](thm.html#ModPForms.thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_mem_modPMod_sub_of_qP_mul_mem.lean

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_SwdAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.mem_modPMod_sub_of_qP_mul_mem (p : ℕ) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (F : Type) [Field F] [CharP F p] (k : ℤ) (hpk : ¬ (p : ℤ) ∣ k) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) (hP : SwdAlgebra.qP F * φ ∈ ModPForms.modPMod N' (k + 2) F) :
    φ ∈ ModPForms.modPMod N' (k - ((p : ℤ) - 1)) F := by sorry
