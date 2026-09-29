-- Prove2me | Theorems.Thm_ModularCurve_exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one
-- name    : ModularCurve.exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/0bb731e4-1378-5787-b093-eb601759c2fd
-- title:
--   Every place descends to a rational place over some 𝔽_{p^m}
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$ such that every $a \in K$ satisfies $a^{p^n} = a$ for some $n > 0$, let $\Gamma \le \mathrm{SL}(2,\mathbb{Z})$ be of finite index with $T \in \Gamma$, and write $F_\Gamma(k) =$ `qExpFunctionFieldC k Γ` for the intermediate field of $k((q))$ obtained by adjoining to $k$ all quotients $\mathrm{intSeriesC}\,k\,p_f / \mathrm{intSeriesC}\,k\,p_g$ coming from modular forms $f, g$ of a common weight $k$ for $\Gamma$ (viewed in $\mathrm{GL}(2,\mathbb{R})$) with integral $q$-expansions $p_f, p_g$ and $\mathrm{intSeriesC}\,k\,p_g \neq 0$. Let $w$ be a place of $F_\Gamma(K)$ over $K$, that is, a valuation subring $\mathcal{O}_w \subsetneq F_\Gamma(K)$ containing the image of $K$ and which is a principal ideal ring. Then there exist an integer $m > 0$, a ring homomorphism $\iota_0 : \mathbb{F}_{p^m} \to K$, a ring homomorphism $\iota : F_\Gamma(\mathbb{F}_{p^m}) \to F_\Gamma(K)$ acting on underlying Laurent series by applying $\iota_0$ coefficientwise, and a place $P$ of $F_\Gamma(\mathbb{F}_{p^m})$ over $\mathbb{F}_{p^m}$ such that $\mathcal{O}_P = \iota^{-1}(\mathcal{O}_w)$ and $\deg P = 1$, where $\deg P$ is the $\mathbb{F}_{p^m}$-dimension of the residue field of $\mathcal{O}_P$.
--
--   This is the descent of a place of the $q$-expansion function field over $\overline{\mathbb{F}}_p$ to a rational place of a finite-field form of that field, in the style of the theory of constant field extensions of algebraic function fields. It is used in the proof that a suitable power of the arithmetic Frobenius fixes the given place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one
    (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (w : Place K ↥(qExpFunctionFieldC K Γ)) :
    ∃ (m : ℕ) (_ : 0 < m) (ι₀ : GaloisField p m →+* K)
      (ι : ↥(qExpFunctionFieldC (GaloisField p m) Γ) →+* ↥(qExpFunctionFieldC K Γ))
      (_ : ∀ x : ↥(qExpFunctionFieldC (GaloisField p m) Γ),
        (ι x : LaurentSeries K) = coeffMap ι₀ (x : LaurentSeries (GaloisField p m)))
      (P : Place (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ)),
      P.toValuationSubring = w.toValuationSubring.comap ι ∧ P.deg = 1 := by sorry
