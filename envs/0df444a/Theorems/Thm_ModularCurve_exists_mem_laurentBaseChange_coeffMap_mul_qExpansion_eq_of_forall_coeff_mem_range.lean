-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
-- name    : ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/bf566896-2fc6-5eeb-9dae-512945f358e7
-- title:
--   Rationality of quotients of modular forms on Γ_H(N)
-- statement:
--   Fix $N \ge 1$ and a subgroup $H \le (\mathbb{Z}/N\mathbb{Z})^{\times}$, and let $\Gamma_H(N)$ be the subgroup [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N\mathbb{Z})^{\times}$ sending $\gamma$ to the reduction of its lower-right entry, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $k \in \mathbb{Z}$ and let $\Phi, \Psi$ be modular forms of weight $k$ for this group, with $\Psi \ne 0$. Let $L$ be a field of characteristic zero and $\iota \colon L \to \mathbb{C}$ a ring homomorphism, and assume that for every $n \in \mathbb{N}$ the $n$-th coefficient of the $q$-expansion of period $1$ of $\Phi$, and likewise that of $\Psi$, lies in the image of $\iota$. The conclusion asserts the existence of a Laurent series $x \in L((q))$ lying in [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField N H)`](def/ModularCurve_LaurentCoeff.html#L103) — the intermediate field of $L((q))$ generated over $L$ by the coefficientwise image, under $\mathbb{Q} \to L$, of the intermediate field [`ModularCurve.xHFunctionField N H`](def/ModularCurve_XH.html#L79) of $\mathbb{Q}((q))$ attached to $\Gamma_H(N)$ — such that, after applying $\iota$ to the coefficients of $x$, one has the identity $\iota(x) \cdot \widetilde{\Psi} = \widetilde{\Phi}$ in $\mathbb{C}((q))$, where $\widetilde{\Phi}, \widetilde{\Psi}$ are the $q$-expansions of $\Phi$ and $\Psi$ viewed as Laurent series.
--
--   This is the descent of the modular function $\Phi/\Psi$, whose Fourier coefficients at $\infty$ lie in the subfield $\iota(L) \subseteq \mathbb{C}$, to the $L$-rational structure of the function field of $X_H(N)$; it rests on the existence of bases of spaces of cusp forms with rational $q$-expansion coefficients and on bounded denominators, and it is cited for instance by [`CuspForm.exists_basis_gammaH_qCoeff_mem_range_ratCast`](thm.html#CuspForm.exists_basis_gammaH_qCoeff_mem_range_ratCast) and [`ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion`](thm.html#ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion). Downstream it is used to identify fixed fields of level automorphisms and the $L$-rational models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range.lean

import Mathlib
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (Φ Ψ : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k) (hΨ : Ψ ≠ 0)
    (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ)
    (hΦ : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑Φ)).coeff n ∈ Set.range ι)
    (hΨι : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑Ψ)).coeff n ∈ Set.range ι) :
    ∃ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField N H) ∧
        ModularCurve.coeffMap ι x *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑Ψ)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑Φ)) := by sorry
