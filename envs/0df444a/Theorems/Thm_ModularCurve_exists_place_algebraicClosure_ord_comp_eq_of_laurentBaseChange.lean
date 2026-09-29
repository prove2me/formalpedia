-- Prove2me | Theorems.Thm_ModularCurve_exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange
-- name    : ModularCurve.exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/f75c7e66-2f67-5579-a0cf-8fd32f6b5493
-- title:
--   Places descend along constant field extension of q-expansion fields
-- statement:
--   Let $K$ be an algebraically closed field equipped with a $\mathbb{Q}$-algebra structure, let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$, and let $F(\Gamma) =$ `qExpFunctionFieldC ℚ Γ` be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,p_f / \mathrm{intSeriesC}\,p_g$, where $f,g$ are modular forms of some weight $k$ for $\Gamma$ (viewed inside $\mathrm{GL}_2(\mathbb{R})$) with integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ and $\mathrm{intSeriesC}\,p_g \ne 0$. For a field $L$ over $\mathbb{Q}$ write $L\cdot F(\Gamma)$ for `laurentBaseChange L (qExpFunctionFieldC ℚ Γ)`, the subfield of $L((q))$ generated over $L$ by the image of $F(\Gamma)$ under coefficientwise application of $\mathbb{Q} \to L$. Let $\tau \colon \overline{\mathbb{Q}} \to K$ be a $\mathbb{Q}$-algebra embedding and let $\Psi \colon \overline{\mathbb{Q}}\cdot F(\Gamma) \to K\cdot F(\Gamma)$ be a ring homomorphism which, on underlying Laurent series, acts by applying $\tau$ to each coefficient. Let $P$ be a place of $K\cdot F(\Gamma)$ over $K$ — that is, a valuation subring of $K\cdot F(\Gamma)$ containing the image of $K$, distinct from the whole field and a principal ideal ring — and suppose $\mathrm{ord}_P(\Psi f) \ne 0$ for at least one $f$, where $\mathrm{ord}$ denotes the negative logarithm of the associated height-one adic valuation. Then there exists a place $P_0$ of $\overline{\mathbb{Q}}\cdot F(\Gamma)$ over $\overline{\mathbb{Q}}$ with $\mathrm{ord}_P(\Psi f) = \mathrm{ord}_{P_0}(f)$ for every $f \in \overline{\mathbb{Q}}\cdot F(\Gamma)$.
--
--   This is the invariance of orders under a constant field extension of a one-variable function field with algebraically closed constant field, in the form needed for the function fields of modular curves: a nontrivial place upstairs restricts along the coefficientwise embedding to a place downstairs with identical order function, no ramification occurring. It is used in the computations of orders of functions at places of the base-changed $q$-expansion fields for $\Gamma_0(N)$ and $\Gamma_1(N)$, and in the counting of places by double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (τ : AlgebraicClosure ℚ →ₐ[ℚ] K)
    (Ψ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) →+*
           ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hΨ : ∀ f, ((Ψ f : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ))) : LaurentSeries K)
             = ModularCurve.coeffMap τ.toRingHom (f : LaurentSeries (AlgebraicClosure ℚ)))
    (P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hP : ∃ f, P.ord (Ψ f) ≠ 0) :
    ∃ P₀ : AlgebraicCurve.Place (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)),
      ∀ f, P.ord (Ψ f) = P₀.ord f := by sorry
