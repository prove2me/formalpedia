-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_sup_adjoin_qExpand_jqModC_eq_one_or_eq_add_one
-- name    : ModularCurve.relfinrank_sup_adjoin_qExpand_jqModC_eq_one_or_eq_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/13c2e412-5982-542a-a7a1-57230f866086
-- title:
--   Degree of j(q^ℓ) over a field containing j(q) is 1 or ℓ+1
-- statement:
--   Let $K$ be a field and $\ell$ a prime which is invertible in the sense that the image of $\ell$ in $K$ is non-zero. Write $K((q))$ for the field of Laurent series (Hahn series over $\mathbb{Z}$) with coefficients in $K$, and let $j =$ `jqModC K` be the element $q^{-1}$ times the image in $K[[q]]$ of the integral power series `jNum` $= E_4^3\cdot\eta^{-24}$-type unit (the $q$-expansion of the modular invariant up to its additive constant), its coefficients transported along $\mathbb{Z}\to K$. Let `qExpand K ℓ` be the ring endomorphism of $K((q))$ substituting $q^{\ell}$ for $q$, i.e. re-indexing a Hahn series along multiplication by $\ell$ on $\mathbb{Z}$, so that `qExpand K ℓ (jqModC K)` is $j(q^{\ell})$. Let $F$ be an intermediate field of $K \subseteq K((q))$ with $j \in F$. Then the relative degree of the compositum $F \vee K(j(q^{\ell}))$ over $F$, where $K(j(q^{\ell}))$ is the intermediate field generated over $K$ by $j(q^{\ell})$, equals either $1$ or $\ell+1$; in particular it is finite.
--
--   This is the degree dichotomy coming from the modular equation $\Phi_{\ell}(j(q), j(q^{\ell})) = 0$: the minimal polynomial of $j(q^{\ell})$ over any field of Laurent series containing $j(q)$ divides a polynomial of degree $\ell+1$ whose remaining $\ell$ roots are permuted cyclically, so it has degree $1$ or $\ell+1$. It is used in identifying the $q$-expansion function field of $X_H(N)$ adjoined $j(q^{\ell})$ with that of $\Gamma_H(N)\cap\Gamma_0(\ell)$ for $\ell \nmid N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_sup_adjoin_qExpand_jqModC_eq_one_or_eq_add_one.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.relfinrank_sup_adjoin_qExpand_jqModC_eq_one_or_eq_add_one
    (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ((ℓ : ℕ) : K) ≠ 0)
    (F : IntermediateField K (LaurentSeries K)) (hj : jqModC K ∈ F) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    IntermediateField.relfinrank F (F ⊔ IntermediateField.adjoin K {qExpand K ℓ (jqModC K)}) = 1 ∨
      IntermediateField.relfinrank F (F ⊔ IntermediateField.adjoin K {qExpand K ℓ (jqModC K)}) = ℓ + 1 := by sorry
