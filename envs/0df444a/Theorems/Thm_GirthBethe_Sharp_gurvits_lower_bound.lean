-- Prove2me | Theorems.Thm_GirthBethe_Sharp_gurvits_lower_bound
-- name    : GirthBethe.Sharp.gurvits_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:20:51.525196+00:00
-- url     : https://prove2.me/theorems/21ba7a0f-da7e-412d-9a0f-fdd7d58a6e6d
-- title:
--   §1.2 eq. (1.4) — Gurvits: $\mathrm{Bethe}(A)\le\mathrm{per}(A)$
-- statement:
--   Let $n\ge1$ and let $A\in\mathbb R^{n\times n}$ have nonnegative entries. Then
--   $$\mathrm{Bethe}(A)\le\mathrm{per}(A),$$
--   where $\mathrm{per}(A)=\sum_{\sigma\in\mathrm{Sym}(n)}\prod_i A_{i,\sigma(i)}$ and $\mathrm{Bethe}(A)$ is the Bethe permanent (1.1).
--
--   This is Gurvits's inequality, the lower half of the paper's main theorem.
--
--   **Formalization Note** Entries may vanish or be irrational; no positivity of the permanent is assumed.
--
--   Differences from the source:
--   - encoding: A ∈ ℝ^{n×n}_{≥0} with rows and columns indexed by [n] → A : Matrix (Fin n) (Fin n) ℝ with ∀ i j, 0 ≤ A i j (0-based indices); reason: relabelling only
--   - encoding: per(A) = ∑_σ ∏_i A_{i,σ(i)} → Matrix.permanent A = ∑_σ ∏_i A_{σ(i), i}; reason: the two sums agree under σ ↦ σ⁻¹
--   - encoding: Bethe(A) := max over PM(G_A) in (1.1) → bethe A := sSup of the Bethe objective over PM(G_A) (0 if PM(G_A) = ∅), real powers with x^0 = 1; reason: the maximum is attained (item bethe_max_attained), so the supremum is the maximum; real powers give the boundary values 1 at p_e = 0 and A_e at p_e = 1, which are the limits by continuity
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 2, §1.2, equation (1.4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_BethePermanent

open Finset

namespace GirthBethe.Sharp

/-- §1.2, equation (1.4) (Gurvits): `Bethe(A) ≤ per(A)` for every nonnegative matrix `A`. -/
theorem gurvits_lower_bound (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) :
    bethe A ≤ A.permanent := by sorry

end GirthBethe.Sharp
