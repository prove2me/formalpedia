-- Prove2me | Theorems.Thm_ModularCurve_diamondOneBar_mul_of_coprime
-- name    : ModularCurve.diamondOneBar_mul_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/859ac1c9-c8f2-5b47-b565-0c2c82c204ff
-- title:
--   Multiplicativity of the diamond operators on J₁(M)
-- statement:
--   Let $M$ be a natural number, assumed nonzero. Write $F =$ [`ModularCurve.x1FunctionField M`](def/ModularCurve_X1.html#L137) for the $q$-expansion function field of $\Gamma_1(M)$ inside $\mathbb{Q}((q))$, and $\bar F =$ [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182) for the intermediate field of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of $F$. The hypothesis `hdia` asserts that for every natural number $d$ coprime to $M$ two things hold: first, there is a $\mathbb{Q}$-algebra automorphism $\sigma_0$ of $F$ with the diamond property for $d$, i.e. $d$ is coprime to $M$ and for every weight $k \in \mathbb{Z}$, all modular forms $f, g$ of weight $k$ on $\Gamma_1(M)$, all integral power series $p_f, p_g$ that are the $q$-expansions of $f$ and $g$ with the Laurent series of $p_g$ nonzero, and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ whose upper-left entry is $\equiv d \bmod M$, the image in $\mathbb{C}((q))$ of $\sigma_0(p_f/p_g)$ times the $q$-expansion of $g|_k\gamma$ equals that of $f|_k\gamma$; second, there is an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma'$ of $\bar F$ extending the chosen automorphism [`ModularCurve.diamondAut M d`](def/ModularCurve_X1Diamond.html#L66) of $F$ coefficientwise, i.e. $\sigma'$ carries the image of each $y \in F$ to the image of $\sigma_0(y)$ for that chosen $\sigma_0$. Then for all natural numbers $d, d'$ coprime to $M$, the endomorphisms [`ModularCurve.diamondOneBar`](def/ModularCurve_X1Diamond.html#L98) of the group [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186), obtained from the semilinear automorphisms attached to `diamondAutBar`, satisfy $\langle dd'\rangle_* = \langle d\rangle_* \langle d'\rangle_*$, the product being composition in the ring of $\mathbb{Z}$-linear endomorphisms.
--
--   This is the multiplicativity of the covariant diamond operators acting on the degree-zero divisor class group of $X_1(M)$ over $\overline{\mathbb{Q}}$, the first step towards an action of $(\mathbb{Z}/M\mathbb{Z})^\times$ by the diamond operators. It is used in the comparison of Hecke actions on $J_1(M)$ and in identities for sums of diamond operators applied to norm-free endomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondOneBar_mul_of_coprime.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.diamondOneBar_mul_of_coprime (M : ℕ) [NeZero M]
    (hdia : ∀ d : ℕ, Nat.Coprime d M →
      (∃ σ₀ : ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M,
          ModularCurve.IsDiamondAut M d σ₀) ∧
        ∃ σ' : ModularCurve.x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ]
            ModularCurve.x1FunctionFieldBar M,
          ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M d) σ')
    (d d' : ℕ) (hd : Nat.Coprime d M) (hd' : Nat.Coprime d' M) :
    ModularCurve.diamondOneBar M (d * d') =
      ModularCurve.diamondOneBar M d * ModularCurve.diamondOneBar M d' := by sorry
