-- Prove2me | Theorems.Thm_ModularCurve_le_span_setOf_logarithmic_of_forall_mem_regularDifferentials_of_frobPushDiffModL_surjOn
-- name    : ModularCurve.le_span_setOf_logarithmic_of_forall_mem_regularDifferentials_of_frobPushDiffModL_surjOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/7a44be7c-1a85-517b-b545-33c9fe4405b0
-- title:
--   Cartier-surjective subspaces consist of logarithmic regular differentials
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $\Gamma\le \mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index containing the translation matrix `ModularGroup.T`, and write $F=$ [`ModularCurve.qExpFunctionFieldC K`](def/ModularCurve_X1.html#L101)$\,\Gamma$ for the intermediate field of $K \subseteq K((q))$ generated over $K$ by the quotients $f/g$ of $K$-reductions of integral $q$-expansions of modular forms of equal weight for $\Gamma$. Let $W$ be a $K$-subspace of [`ModularCurve.ssPolarDifferentials K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L35), the space of $\omega\in\Omega_{F/K}$ that are regular at every place of $F/K$ outside the supersingular set `ssPlacesQExp K Γ p` and have at most a simple pole at each place of that set, where a place is a valuation subring of $F$, other than $F$ itself, containing the image of $K$ and with principal ideal structure. Assume (i) every $w\in W$ lies in [`AlgebraicCurve.regularDifferentials`](def/AlgebraicCurve_RegularDifferentials.html#L26), i.e. for each place $v$ one has $w = f\cdot d(\pi_v)$ with $f$ in the valuation ring of $v$ and $\pi_v$ a uniformiser; and (ii) $W$ is contained in the image of $W$ under [`ModularCurve.frobPushDiffModL K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L103), the chosen $K$-linear operator whose effect on $q$-expansions of differentials is decimation $a_n\mapsto a_{pn}$ (and $0$ if no such operator exists). Then $W$ is contained in the $K$-span of those $\eta$ in `ssPolarDifferentials K Γ p` which are regular in the above sense and satisfy $\eta = f^{-1}\,df$ for some $f\in F$, $f\neq 0$.
--
--   This is the Cartier–Serre description of the differentials fixed by the Cartier operator: a space of regular supersingular-polar differentials onto which the Frobenius push-forward (the $q$-expansion decimation realising $U_p$) maps surjectively is spanned by logarithmic forms $f^{-1}df$. It feeds the count of regular differentials in the ordinary corner used in the Raynaud-type comparison of the relative Picard group with the set of supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_le_span_setOf_logarithmic_of_forall_mem_regularDifferentials_of_frobPushDiffModL_surjOn.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups

theorem ModularCurve.le_span_setOf_logarithmic_of_forall_mem_regularDifferentials_of_frobPushDiffModL_surjOn
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (W : Submodule K ↥(ModularCurve.ssPolarDifferentials K Γ p))

    (hWreg : ∀ w ∈ W, ((w : ↥(ModularCurve.ssPolarDifferentials K Γ p)) : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) ∈
      AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K Γ))

    (hWC : ∀ w' ∈ W, ∃ w ∈ W,
      ((w' : ↥(ModularCurve.ssPolarDifferentials K Γ p)) : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) =
        ModularCurve.frobPushDiffModL K Γ p ((w : ↥(ModularCurve.ssPolarDifferentials K Γ p)) : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])) :
    W ≤ Submodule.span K {η : ↥(ModularCurve.ssPolarDifferentials K Γ p) |
        ((η : ↥(ModularCurve.ssPolarDifferentials K Γ p)) : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) ∈
            AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K Γ) ∧
        (∃ f : ModularCurve.qExpFunctionFieldC K Γ, f ≠ 0 ∧
          ((η : ↥(ModularCurve.ssPolarDifferentials K Γ p)) : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) =
            f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K Γ) f)} := by sorry
