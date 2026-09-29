-- Prove2me | Theorems.Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective
-- name    : ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/d72f2dd3-ef08-57e8-ac50-119747d6166e
-- title:
--   Integral weight-two cusp forms and regular differentials on X₁(M)_k
-- statement:
--   Let $k$ be an algebraically closed field, let $M$ be a positive integer with $M \neq 0$ in $k$, and let $L$ denote the $\mathbb{Z}$-submodule of $\mathrm{CuspForm}(\Gamma_1(M), 2)$ spanned by those weight-two cusp forms $f$ on $\Gamma_1(M)$ whose translates $f \mid_2 \gamma$, for every $\gamma \in \Gamma_0(M) \subseteq \mathrm{SL}_2(\mathbb{Z})$, have all width-one $q$-expansion coefficients [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) in the image of $\mathbb{Z} \to \mathbb{C}$. Write $F =$ [`ModularCurve.x1FunctionFieldC k M`](def/ModularCurve_X1.html#L134) for the intermediate field of $k((q))$ generated over $k$ by the set `intFormRatiosC k (Gamma1 M)`, and $\Omega$ for the $k$-submodule [`AlgebraicCurve.regularDifferentials`](def/AlgebraicCurve_RegularDifferentials.html#L26) of $\Omega[F/k]$ consisting of the Kähler differentials $\omega$ such that at every place $v$ of $F/k$ (a proper valuation subring of $F$ containing $k$ whose ideals are principal) one has $\omega = f \cdot D(\pi_v)$ for some $f$ in the valuation subring of $v$, $\pi_v$ a uniformiser. The assertion is twofold. First, there is a $k$-linear isomorphism $e : k \otimes_{\mathbb{Z}} L \xrightarrow{\sim} \Omega$ compatible with $q$-expansions, in the sense that for all $c \in k$, $f \in L$ and $a : \mathbb{N} \to \mathbb{Z}$ with $n$-th $q$-coefficient of $f$ equal to $a_n$ for every $n$, the image of $e(c \otimes f)$ under [`ModularCurve.qExpansionDiffAlong`](def/ModularCurve_QExpansionDiff.html#L42) applied to the inclusion $F \hookrightarrow k((q))$ — the $k$-linear map $\Omega[F/k] \to k((q))$ characterised, when it exists and taken to be zero otherwise, by sending $D x$ to `thetaL` of the Laurent expansion of $x$ and by satisfying $\varphi(f \cdot \omega) = x \mapsto$ (Laurent expansion of $f$) times $\varphi(\omega)$ — equals $c \cdot \sum_n a_n q^n$ in $k((q))$. Second, this $q$-expansion map is injective on $\Omega$.
--
--   This is the $q$-expansion principle for $X_1(M)$ in characteristic prime to $M$: the integral lattice of weight-two cusp forms on $\Gamma_1(M)$, base-changed to $k$, is identified with the space of regular differentials on the $q$-expansion function field of $X_1(M)$ over $k$, and a regular differential is determined by its $q$-expansion at the cusp $\infty$. It is used in the computation of the order of the torsion subgroup attached to the Hecke operator $T_1$ via a characteristic polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct ModularForm MatrixGroups

theorem ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective
    (k : Type*) [Field k] [IsAlgClosed k] (M : ℕ) [NeZero M] (hM : (M : k) ≠ 0) :
    (∃ e : k ⊗[ℤ] ↥(Submodule.span ℤ
          {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2 |
            ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
              ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n ∈
                Set.range ((↑) : ℤ → ℂ)}) ≃ₗ[k]
        ↥(AlgebraicCurve.regularDifferentials k ↥(ModularCurve.x1FunctionFieldC k M)),
      ∀ (c : k)
        (f : ↥(Submodule.span ℤ
          {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2 |
            ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
              ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n ∈
                Set.range ((↑) : ℤ → ℂ)}))
        (a : ℕ → ℤ),
        (∀ n : ℕ, ModularFormClass.qCoeff
            ((f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) : UpperHalfPlane → ℂ) n = (a n : ℂ)) →
        ModularCurve.qExpansionDiffAlong (ModularCurve.x1FunctionFieldC k M).val
            (e (c ⊗ₜ[ℤ] f) : Ω[↥(ModularCurve.x1FunctionFieldC k M)⁄k]) =
          c • HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun n => (a n : k))) ∧
    Function.Injective
      (fun ω : ↥(AlgebraicCurve.regularDifferentials k ↥(ModularCurve.x1FunctionFieldC k M)) =>
        ModularCurve.qExpansionDiffAlong (ModularCurve.x1FunctionFieldC k M).val
          (ω : Ω[↥(ModularCurve.x1FunctionFieldC k M)⁄k])) := by sorry
