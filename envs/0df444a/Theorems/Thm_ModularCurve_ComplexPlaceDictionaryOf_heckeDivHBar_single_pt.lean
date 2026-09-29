-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt
-- name    : ModularCurve.ComplexPlaceDictionaryOf.heckeDivHBar_single_pt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/aeca0052-466d-5374-8e71-8f82a36f63d9
-- title:
--   Hecke correspondence on a point divisor of X_H(M)
-- statement:
--   Fix $M\ge 1$, a subgroup $H\le(\mathbb{Z}/M)^\times$, and let $\Gamma_H(M)$ be the subgroup of $SL(2,\mathbb{Z})$ obtained by pulling $H$ back along the lower-right-entry character of $\Gamma_0(M)$. Let $D$ be a complex place dictionary for $\Gamma_H(M)$ and the $q$-expansion function field $F_0=$ `xHFunctionField M H`: that is, an assignment $\tau\mapsto D.\mathrm{pt}(\tau)$ of places of $\mathbb{C}\cdot F_0$ to points of $\mathbb{H}$, together with positive ramification numbers, invariant under $\Gamma_H(M)$, whose valuation subrings consist of those $x$ whose analytic realisation is bounded near $\tau$, and for which $\mathrm{meromorphicOrderAt}$ of the realisation at $\tau$ is the ramification number times $\mathrm{ord}_{D.\mathrm{pt}(\tau)}(x)$. Let $\ell$ be a prime such that $q\mapsto q^\ell$ carries $F_0$ into the function field of $\Gamma_H(M)\cap\Gamma_0(M\ell)$, such that both degeneracy maps $\bar\alpha,\bar\beta$ into $\mathbb{C}\cdot F(\Gamma_H(M)\cap\Gamma_0(M\ell))$ are integral ring homomorphisms, and such that the latter field has principal divisors (every nonzero element has a degree-zero divisor computing its orders). Let $\tau\in\mathbb{H}$. Then, writing $T=\bar\alpha_*\circ\bar\beta^*$ for `heckeDivHBar`: first, if $\ell\nmid M$ then for every $\rho\in\Gamma_0(M)$ whose lower-right entry reduces to $\ell$ mod $M$, $$T\,[D.\mathrm{pt}(\tau)]=\sum_{j=0}^{\ell-1}\big[D.\mathrm{pt}(\beta_j\tau)\big]+\big[D.\mathrm{pt}((\rho\cdot\mathrm{diag}(\ell,1))\tau)\big],$$ with $\beta_j=\begin{pmatrix}1&j\\0&\ell\end{pmatrix}$; second, if $\ell\mid M$ then $T\,[D.\mathrm{pt}(\tau)]=\sum_{j=0}^{\ell-1}[D.\mathrm{pt}(\beta_j\tau)]$. Both equalities are equalities of divisors, so coinciding points contribute with added multiplicity.
--
--   This is the classical description of the Hecke correspondence $T_\ell$ (respectively $U_\ell$ when $\ell\mid M$) on the modular curve $X_H(M)$, evaluated on the divisor of a single non-cuspidal point: the $\ell+1$ (respectively $\ell$) coset representatives of $\Gamma_H(M)\,\mathrm{diag}(1,\ell)\,\Gamma_H(M)$, the last one twisted by the diamond operator $\langle\ell\rangle$. It is used in the comparison of the divisorial Hecke action with the Hecke action on the Jacobian via the Abel–Jacobi map modulo the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane in
open scoped MatrixGroups in

theorem ModularCurve.ComplexPlaceDictionaryOf.heckeDivHBar_single_pt
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (h0 : ModularCurve.HeckeBetaHDefined M H ℓ)
    (hα : ModularCurve.HeckeAlphaHBarIntegral ℂ M H ℓ) (hβ : ModularCurve.HeckeBetaHBarIntegral ℂ M H ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (τ : UpperHalfPlane) :
    (∀ (hℓM : ¬ ℓ ∣ M) (ρ : CongruenceSubgroup.Gamma0 M), (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ →
      ModularCurve.heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
        ∑ j ∈ Finset.range ℓ, Finsupp.single (D.pt (ModularForm.heckeMatrix ℓ j • τ)) 1 +
          Finsupp.single (D.pt (((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) • τ)) 1) ∧
    (ℓ ∣ M →
      ModularCurve.heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
        ∑ j ∈ Finset.range ℓ, Finsupp.single (D.pt (ModularForm.heckeMatrix ℓ j • τ)) 1) := by sorry
