-- Prove2me | Theorems.Thm_LineVsPoint_lemma_2_3
-- name    : LineVsPoint.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:03:54.289408+00:00
-- url     : https://prove2.me/theorems/5ac4fbf1-0c14-4c2d-915b-fa135f861de6
-- title:
--   Lemma 2.3 — a generic direction $\lambda\in\mathbb F_q^3$ with $\gcd(B,D_\lambda B)=1$
-- statement:
--   **Lemma 2.3.** Let $\mathbb F_q$ be a finite field and let $B\in\mathbb F_q[X,Y,Z]$ be nonzero and squarefree with $\deg B<q$. There is a vector $\lambda=(\lambda_X,\lambda_Y,\lambda_Z)\in\mathbb F_q^3$ such that
--
--   $$
--   D_\lambda:=\lambda_X\partial_X+\lambda_Y\partial_Y+\lambda_Z\partial_Z\quad\text{satisfies}\quad \gcd(B,D_\lambda B)=1 .
--   $$
--
--   Here $\deg$ is the total degree, derivatives are formal, and $\gcd=1$ means that the only common divisors of $B$ and $D_\lambda B$ are nonzero constants. The point is that $\lambda$ lies in $\mathbb F_q^3$ itself, with no field extension; Section 3 uses it to make every surviving root simple.
--
--   Differences from the source:
--   - encoding: gcd(B, D_λB) = 1 (coprime: only nonzero constants divide both, §2.1) → IsRelPrime B (dirDeriv λ B); reason: IsRelPrime is exactly 'every common divisor is a unit'; IsCoprime (Bézout) would be a different, stronger notion
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 2.3, pp.11–12

import Definitions.Def_LineVsPoint_dirDeriv

set_option autoImplicit false

universe u

namespace LineVsPoint

/-- **Lemma 2.3** (generic direction). *Let `B ∈ F_q[X, Y, Z]` be nonzero and squarefree with
`deg B < q`. There is a vector `λ = (λ_X, λ_Y, λ_Z) ∈ F³_q` such that
`D_λ := λ_X ∂_X + λ_Y ∂_Y + λ_Z ∂_Z` satisfies `gcd(B, D_λ B) = 1`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Lemma 2.3, pp.11–12.

**Formalization Note.** `deg` is the total degree; "`gcd = 1`" (coprime: the only common divisors
are nonzero constants, §2.1, p.10) is `IsRelPrime`, not the Bézout notion `IsCoprime`. -/
theorem lemma_2_3 :
    ∀ (F : Type u) [Field F] [Fintype F] (B : MvPolynomial (Fin 3) F), B ≠ 0 → Squarefree B →
      B.totalDegree < Fintype.card F →
      ∃ lam : Fin 3 → F, IsRelPrime B (dirDeriv lam B) := by sorry

end LineVsPoint
