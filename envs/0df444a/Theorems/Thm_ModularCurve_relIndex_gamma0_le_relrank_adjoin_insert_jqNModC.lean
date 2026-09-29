-- Prove2me | Theorems.Thm_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
-- name    : ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/28febe38-f219-5a6b-9011-6af36e0a6d1f
-- title:
--   Degree of j(q^N) bounds the index of Γ∩Γ₀(N)
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$ containing the translation matrix `ModularGroup.T`, and let $N$ be a non-zero natural number. Inside the field $\mathbb C((q))$ of Laurent series consider the set $S$ of all quotients $F/G$, where $F$ and $G$ are the images in $\mathbb C((q))$ of the $q$-expansions of period $1$ at $\infty$ of two modular forms $f,g$ of one and the same weight $k\in\mathbb Z$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb R)$, subject to the $q$-expansion of $g$ being non-zero; let $A$ be the subfield of $\mathbb C((q))$ generated over $\mathbb C$ by $S$. Let $j_N =$ [`ModularCurve.jqNModC ℂ N`](def/ModularCurve_JqCoeff.html#L18) be the Laurent series obtained from $q^{-1}$ times the integral power series `jNum` (the $q$-expansion of $j$) by the ring homomorphism multiplying all exponents by $N$, that is $j(q)$ with $q$ replaced by $q^N$. The assertion is that the index of $\Gamma\cap\Gamma_0(N)$ in $\Gamma$, viewed as a cardinal, is at most the relative rank of $A$ in the subfield of $\mathbb C((q))$ generated over $\mathbb C$ by $S\cup\{j_N\}$, i.e. at most the degree $[A(j_N):A]$, which is not asserted to be finite.
--
--   This is the "enough conjugates" half of the computation of the degree of the degeneracy covering $X(\Gamma\cap\Gamma_0(N))\to X(\Gamma)$, the lower bound complementing the norm argument giving $[A(\Gamma'):A(\Gamma)]\le[\Gamma:\Gamma']$. It is used in the determination of the ranks of the function fields attached to the Hecke correspondences $\alpha$ on $X_0$-type curves and in the base-change comparisons of those function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)
    (N : ℕ) [NeZero N] :
    (((CongruenceSubgroup.Gamma0 N).relIndex Γ : ℕ) : Cardinal) ≤
      IntermediateField.relrank
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})
        (IntermediateField.adjoin ℂ (insert (ModularCurve.jqNModC ℂ N)
          {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})) := by sorry
