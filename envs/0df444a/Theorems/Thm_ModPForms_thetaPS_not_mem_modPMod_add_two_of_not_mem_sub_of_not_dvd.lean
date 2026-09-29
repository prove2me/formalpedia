-- Prove2me | Theorems.Thm_ModPForms_thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_of_not_dvd
-- name    : ModPForms.thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/89ccf9f5-8983-5d4f-9e33-35754ce1b21e
-- title:
--   Theta raises the filtration when p ∤ k
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $N'$ be a nonzero natural number with $p \nmid N'$, and let $F$ be a field of characteristic $p$. For an integer $j$ write $\mathrm{modPMod}\,N'\,j\,F$ for the $F$-submodule of $F[[q]]$ spanned by those power series $\mathrm{mk}\,(n \mapsto (a_n \bmod p))$ arising from a modular form $f$ of weight $j$ on $\Gamma_0(N')$ together with integers $a_n$ such that the $n$-th coefficient of the $q$-expansion of $f$ (at width $1$) equals $a_n$ for all $n$; and let $\theta$ be the operator $\mathrm{thetaPS}$ sending $\varphi$ to the power series with $n$-th coefficient $n \cdot \mathrm{coeff}_n \varphi$. Let $k$ be an integer with $p \nmid k$ and let $\varphi \in F[[q]]$ satisfy $\varphi \in \mathrm{modPMod}\,N'\,k\,F$ and $\varphi \notin \mathrm{modPMod}\,N'\,(k-(p-1))\,F$. Then $\theta\varphi \notin \mathrm{modPMod}\,N'\,(k+2)\,F$. The conclusion is thus the single exclusion in weight $k+2$, not the full determination of the filtration of $\theta\varphi$ as $k+p+1$.
--
--   This is the standard statement that the theta operator strictly raises the filtration of a mod $p$ modular form whose weight is prime to $p$: a form of exact filtration $k$ with $p \nmid k$ has $\theta\varphi$ outside weight $k+2$. It is used in the mod $p$ part of the level-lowering input, being cited in the analysis of integral $q$-expansion lattices and in the recognition of forms of weight two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_of_not_dvd.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_of_not_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (F : Type) [Field F] [CharP F p] (k : ℤ) (hpk : ¬ (p : ℤ) ∣ k)
    (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F) (hlow : φ ∉ modPMod N' (k - ((p : ℤ) - 1)) F) :
    thetaPS φ ∉ modPMod N' (k + 2) F := by sorry
