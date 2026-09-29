-- Prove2me | Theorems.Thm_ModPForms_finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two
-- name    : ModPForms.finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/a57e75a7-778a-52d3-9746-bd24d08c8a71
-- title:
--   Kernel of Uₚ on mod-p weight-2 forms of level Np
-- statement:
--   Let $p$ be a prime, let $N$ be a nonzero natural number with $p \nmid N$, and let $F$ be any field (no assumption is made on its characteristic). For a level $M$, a weight $k$ and a field $F$, the submodule $\mathrm{modPCusp}\,M\,k\,F \subseteq F[[X]]$ is defined as the $F$-span of those power series $\varphi$ for which there exist a cusp form $f$ of weight $k$ on $\Gamma_0(M)$ and a sequence of integers $(a_n)_{n \in \mathbb{N}}$ such that the $n$-th $q$-expansion coefficient of $f$ (the $n$-th coefficient of its $q$-expansion at period $1$) equals $a_n$ for every $n$, and $\varphi = \sum_n \overline{a_n} X^n$ with $\overline{a_n}$ the image of $a_n$ in $F$. The operator [`PowerSeries.heckeU p`](def/PowerSeries_FormalHeckeOperators.html#L11) is the $F$-linear endomorphism of $F[[X]]$ sending $f$ to $\sum_n (\text{coeff}_{pn} f) X^n$. The assertion is that the kernel of the restriction of this operator to the submodule $\mathrm{modPCusp}\,(N p)\,2\,F$, i.e. the set of elements of that submodule annihilated by $U_p$, has $F$-dimension at most the $F$-dimension of $\mathrm{modPCusp}\,N\,2\,F$.
--
--   This is the bound on the degeneracy of $U_p$ on the mod-$p$ reductions of integral weight-2 cusp forms of level $Np$ at a prime $p$ exactly dividing the level, coming from the fact that $U_p$ has determinant $\pm p^{\dim S_2(\Gamma_0(N))}$ on the weight-2 cusp forms of level $Np$. It is used in the comparison of the mod-$p$ reductions of cusp forms of weight $p+1$ and level $N$ with those of weight $2$ and level $Np$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two.lean

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (F : Type) [Field F] :
    Module.finrank F
        ↥(LinearMap.ker ((PowerSeries.heckeU p : PowerSeries F →ₗ[F] PowerSeries F).domRestrict
          (ModPForms.modPCusp (N * p) 2 F)))
      ≤ Module.finrank F ↥(ModPForms.modPCusp N 2 F) := by sorry
