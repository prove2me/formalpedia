-- Prove2me | Theorems.Thm_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
-- name    : IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/141c7e0a-7a15-56de-87bb-ab6427af936b
-- title:
--   Kummer extensions: B ≅ R[T]/(T^e-t) for regular R
-- statement:
--   Let $R$ be a regular local domain with $\operatorname{ringKrullDim} R \le 2$, let $t \in \mathfrak{m}_R$ with $t \notin \mathfrak{m}_R^2$, and let $e$ be a positive natural number. Let $B$ be an integrally closed domain equipped with an $R$-algebra structure that makes it module-finite over $R$ and for which the scalar action is faithful (so $R \to B$ is injective). Let $K_0$ be a field that is a fraction field of $R$, and let $F$ be a field that is simultaneously a $K_0$-algebra and an $R$-algebra compatibly, and a $B$-algebra compatibly over $R$, realising $F$ as a fraction field of $B$; assume $\operatorname{finrank}_{K_0} F = e$. Finally let $\theta \in B$ satisfy $\theta^e = t$ (image of $t$ under $R \to B$). The conclusion asserts the existence of an isomorphism of $R$-algebras $\varphi : R[X]/(X^e - C\,t) \xrightarrow{\sim} B$, given as `AdjoinRoot` of the polynomial $X^e - C\,t$ over $R$, sending the distinguished root `AdjoinRoot.root` to $\theta$.
--
--   This is the normality (or Abhyankar–Kummer) recognition step: a finite normal cover of a regular local base of dimension at most two, of generic degree $e$ and containing an $e$-th root of a regular parameter $t$, is exactly the Kummer algebra $R[T]/(T^e - t)$. It is used in the construction of explicit Kummer models of totally ramified cyclic covers, feeding the base-change and primitive-root versions that follow; the proof combines the regularity of $R[T]/(T^e-t)$ with unique factorisation in dimension at most two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (hdim : ringKrullDim R ≤ 2)
    {t : R} (ht : t ∈ maximalIdeal R) (ht2 : t ∉ maximalIdeal R ^ 2) {e : ℕ} (he : 0 < e)
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    (hdeg : Module.finrank K₀ F = e)
    (θ : B) (hθ : θ ^ e = algebraMap R B t) :
    ∃ φ : AdjoinRoot (X ^ e - C t : R[X]) ≃ₐ[R] B, φ (AdjoinRoot.root (X ^ e - C t : R[X])) = θ := by sorry
