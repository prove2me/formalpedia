-- Prove2me | Theorems.Thm_ModPForms_thetaPS_mem_modPMod_add_of_mem
-- name    : ModPForms.thetaPS_mem_modPMod_add_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/61f0b60a-1bdb-5f37-8a23-584d533beb24
-- title:
--   The theta operator raises mod p weight by p+1
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $N'$ be a nonzero natural number, let $k$ be an integer, and let $F$ be a field of characteristic $p$. For a power series $\varphi \in F[[q]]$, write $\theta\varphi$ for the power series `thetaPS` $\varphi$ whose $n$-th coefficient is $n \cdot (\text{coeff}_n \varphi)$, the integer $n$ being read in $F$. For an integer $w$, the space `modPMod` $N'\,w\,F$ is the $F$-subspace of $F[[q]]$ spanned by those power series obtained as follows: one takes a modular form $f$ of weight $w$ on $\Gamma_0(N')$ together with a sequence of integers $(a_n)_{n \ge 0}$ such that the $n$-th coefficient of the $q$-expansion of $f$ (at width $1$) equals $a_n$ for every $n$, and forms the power series with coefficients the images of the $a_n$ in $F$. The assertion is that if $\varphi$ lies in `modPMod` $N'\,k\,F$, then $\theta\varphi$ lies in `modPMod` $N'\,(k + (p+1))\,F$.
--
--   This is the classical statement that the Ramanujan operator $\theta = q\,d/dq$ raises the weight of a mod $p$ modular form of level $N'$ by $p+1$, here formulated for the $F$-spans of reductions of integral $q$-expansions of weight-$k$ forms on $\Gamma_0(N')$. It is used in the mod $p$ weight bookkeeping of the present development, notably by [`ModPForms.mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero`](thm.html#ModPForms.mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero); the two inputs it draws on are the existence of a weight $p-1$ form on $\Gamma_0(N')$ with integral coefficients congruent to $1$ mod $p$ and the realisation of the Serre derivative in weight $k+2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_thetaPS_mem_modPMod_add_of_mem.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.thetaPS_mem_modPMod_add_of_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (k : ℤ)
    (F : Type) [Field F] [CharP F p] (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F) :
    thetaPS φ ∈ modPMod N' (k + ((p : ℤ) + 1)) F := by sorry
