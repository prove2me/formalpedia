-- Prove2me | Theorems.Thm_ModularCurve_deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd
-- name    : ModularCurve.deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/049b9283-2018-5877-b81a-6f6d22819462
-- title:
--   Traces of places on 𝔽_{p^m}-forms of q-expansion function fields
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ ($p$ prime) in which every element satisfies $a^{p^n}=a$ for some $n>0$, and let $\Gamma\le \mathrm{SL}_2(\mathbb{Z})$ be of finite index with $T\in\Gamma$. For a field $k$, write $F_\Gamma(k)$ for `qExpFunctionFieldC k Γ`, the intermediate field of $k(\!(q)\!)$ obtained by adjoining to $k$ all ratios $\iota_k(p_f)/\iota_k(p_g)$ of integral $q$-expansions of modular forms of level $\Gamma$ (with $\iota_k(p_g)\neq0$), and recall that a `Place` of such a field over $k$ is a valuation subring containing $k$, different from the whole field and a principal ideal ring, its degree being the $k$-dimension of its residue field. Given a place $w$ of $F_\Gamma(K)$ over $K$; a ring homomorphism $\iota_1\colon F_\Gamma(\mathbb{F}_p)\to F_\Gamma(K)$ acting on Laurent series coefficientwise through $\mathbb{Z}/p\to K$, and a place $P_1$ of $F_\Gamma(\mathbb{F}_p)$ over $\mathbb{F}_p$ whose valuation subring is the preimage under $\iota_1$ of that of $w$; an integer $m>0$, an embedding $\iota_0\colon \mathbb{F}_{p^m}\to K$, a homomorphism $\iota\colon F_\Gamma(\mathbb{F}_{p^m})\to F_\Gamma(K)$ acting coefficientwise through $\iota_0$, and a place $P$ of $F_\Gamma(\mathbb{F}_{p^m})$ over $\mathbb{F}_{p^m}$ whose valuation subring is the preimage under $\iota$ of that of $w$; then $\deg P_1 \mid m$ implies $\deg P = 1$.
--
--   This is the function-field statement that a place of a function field over $\mathbb{F}_p$ becomes rational after the constant field extension to $\mathbb{F}_{p^m}$ as soon as its residue degree divides $m$, applied to the $q$-expansion function fields of level $\Gamma$ and to the traces of a fixed place of the field over the algebraically closed field $K$. It feeds the construction of a rational place of the $\mathbb{F}_{p^m}$-form of the $q$-expansion function field restricting to a given place over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

theorem ModularCurve.deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd
    (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (w : Place K ↥(qExpFunctionFieldC K Γ))

    (ι₁ : ↥(qExpFunctionFieldC (ZMod p) Γ) →+* ↥(qExpFunctionFieldC K Γ))
    (hι₁ : ∀ x : ↥(qExpFunctionFieldC (ZMod p) Γ),
      (ι₁ x : LaurentSeries K) = coeffMap (ZMod.castHom (dvd_refl p) K) (x : LaurentSeries (ZMod p)))
    (P₁ : Place (ZMod p) ↥(qExpFunctionFieldC (ZMod p) Γ))
    (hP₁ : P₁.toValuationSubring = w.toValuationSubring.comap ι₁)

    (m : ℕ) (hm : 0 < m) (ι₀ : GaloisField p m →+* K)
    (ι : ↥(qExpFunctionFieldC (GaloisField p m) Γ) →+* ↥(qExpFunctionFieldC K Γ))
    (hι : ∀ x : ↥(qExpFunctionFieldC (GaloisField p m) Γ),
      (ι x : LaurentSeries K) = coeffMap ι₀ (x : LaurentSeries (GaloisField p m)))
    (P : Place (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ))
    (hP : P.toValuationSubring = w.toValuationSubring.comap ι)
    (hdvd : P₁.deg ∣ m) :
    P.deg = 1 := by sorry
