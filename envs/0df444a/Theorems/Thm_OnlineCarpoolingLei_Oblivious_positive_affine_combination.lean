-- Prove2me | Theorems.Thm_OnlineCarpoolingLei_Oblivious_positive_affine_combination
-- name    : OnlineCarpoolingLei.Oblivious.positive_affine_combination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:18.872314+00:00
-- url     : https://prove2.me/theorems/aa3d5915-d783-46c9-a39c-c606d80a2e41
-- title:
--   Lemma 6.2 — a finite affine cover of a compact convex set has a positive nonnegative combination
-- statement:
--   Let $B\subset\mathbb R^N$ be a nonempty compact convex set and let $\phi_1,\dots,\phi_m:\mathbb R^N\to\mathbb R$ be affine functions. Suppose that
--   $$B=\bigcup_{i=1}^m\{p\in B:\phi_i(p)>0\}.$$
--   Then there exist $\lambda_1,\dots,\lambda_m\ge0$ such that
--   $$\sum_{i=1}^m\lambda_i\phi_i(p)>0\qquad\text{for every }p\in B.$$
--
--   The weights are only required to be nonnegative; they need not sum to one. This finite separation lemma lets the proof of Theorem 3.3 combine finitely many test functions into one. If $m=0$ the hypothesis forces $B=\emptyset$, which is excluded.
--
--   Differences from the source:
--   - encoding: $\mathbb R^N$ → `Fin N → ℝ`; reason: same vector space, topology and convex structure
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Lemma 6.2, p.12 (PDF p.12)

import Mathlib

namespace OnlineCarpoolingLei.Oblivious

/-- Lemma 6.2 (p.12). Let `B ⊂ ℝ^N` be nonempty, compact and convex, and `ϕ₁, …, ϕ_m` affine
functions on `ℝ^N` with `B = ⋃ᵢ {p ∈ B : ϕᵢ(p) > 0}`. Then there are `λ₁, …, λ_m ≥ 0` with
`∑ᵢ λᵢ ϕᵢ(p) > 0` for every `p ∈ B`. -/
theorem positive_affine_combination {N m : ℕ} (B : Set (Fin N → ℝ)) (hB_ne : B.Nonempty)
    (hB_compact : IsCompact B) (hB_convex : Convex ℝ B)
    (ϕ : Fin m → (Fin N → ℝ) →ᵃ[ℝ] ℝ)
    (hcover : B = ⋃ i, {p | p ∈ B ∧ 0 < ϕ i p}) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ ∀ p ∈ B, 0 < ∑ i, lam i * ϕ i p := by sorry

end OnlineCarpoolingLei.Oblivious
