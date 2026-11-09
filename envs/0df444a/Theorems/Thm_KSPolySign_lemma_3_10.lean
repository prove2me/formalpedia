-- Prove2me | Theorems.Thm_KSPolySign_lemma_3_10
-- name    : KSPolySign.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:39:08.39577+00:00
-- url     : https://prove2.me/theorems/b5b2ef00-fb39-4ee7-83a7-86bfe455805f
-- title:
--   Lemma 3.10 — endpoint move
-- statement:
--   Let $y\in[-1,1]^k$ with optimizer $(b,U,V)$, and let $i$ be an active coordinate. For $s\in\{-1,1\}$ let $y^{i,s}$ agree with $y$ except that $y^{i,s}_i=s$. With $\beta_i=\beta(y_i)$, $u_i=a_i^*Ua_i$, $v_i=a_i^*Va_i$:
--
--   1. if $\iota\beta_iv_i\ge1-y_i$, then $(b,U,V)$ is feasible at $y^{i,1}$ and $P(y^{i,1})\le P(y)$;
--   2. if $\iota\beta_iu_i\ge1+y_i$, then $(b,U,V)$ is feasible at $y^{i,-1}$ and $P(y^{i,-1})\le P(y)$.
--
--   At a state that is not light, some coordinate can therefore be fixed without increasing the potential.
--
--   Differences from the source:
--   - generalization: the normalized inputs Ā_i of Lemma 3.1 (F = 0) → every maintained instance: PSD rank-one C_i with ∑C_i² ⪯ I, any Hermitian F, any ρ > 0; reason: Definition 3.5 evaluates this notation with C_i in place of Ā_i, and the normalized inputs are such an instance (ζ ≤ 1); the statement specializes to the source's
--   - encoding: u_i = a_i*Ua_i, v_i = a_i*Va_i for C_i = a_ia_i* → re tr[C_iU], re tr[C_iV]; reason: a_i*Ua_i = tr[C_iU]; same values
--   - encoding: matrices in ℂ^{n×n} with nonzero inputs (so n ≥ 1) → explicit hypothesis 1 ≤ n; reason: excludes only 0×0 matrices, where the program of Definition 3.3 is degenerate and P has no meaning
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.10, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_KSPolySign_IsOptimal
import Definitions.Def_KSPolySign_IsInstance
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 3.10 (Endpoint move).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.10, p.22 (PDF p.22).

Let `y ∈ [−1, 1]^k` with optimizer `(b, U, V)`, and let `i` be active. Let `y^{i,s}` agree with `y`
except `y^{i,s}_i = s`. If `ιβ_iv_i ≥ 1 − y_i`, then `(b, U, V)` is feasible at `y^{i,1}` and
`P(y^{i,1}) ≤ P(y)`. If `ιβ_iu_i ≥ 1 + y_i`, then `(b, U, V)` is feasible at `y^{i,−1}` and
`P(y^{i,−1}) ≤ P(y)`.

**Formalization Note** Stated for every maintained instance (Definition 3.5: nonzero PSD rank-one `C_i` with `∑ C_i² ⪯ I`, a fixed Hermitian `F`) and every `ρ > 0`; the normalized inputs are the case `F = 0`, `C_i = Ā_i`. `n ≥ 1` excludes `0 × 0` matrices. `u_i = a_i*Ua_i = tr[C_iU]` and `v_i = tr[C_iV]` for
`C_i = a_ia_i*`; `y^{i,s}` is `Function.update y i s`. -/
theorem lemma_3_10 (n k : ℕ) (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (hC : IsInstance C)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian) (ρ : ℝ) (hρ : 0 < ρ)
    (y : Fin k → ℝ) (hy : ∀ i, |y i| ≤ 1) (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ) (hopt : IsOptimal C F ρ y b U V)
    (i : Fin k) (hi : |y i| < 1) :
    (1 - y i ≤ iota * beta (y i) * (C i * V).trace.re →
        Feasible C F (Function.update y i 1) b U V ∧
          pot C F ρ (Function.update y i 1) ≤ pot C F ρ y) ∧
      (1 + y i ≤ iota * beta (y i) * (C i * U).trace.re →
        Feasible C F (Function.update y i (-1)) b U V ∧
          pot C F ρ (Function.update y i (-1)) ≤ pot C F ρ y) := by sorry

end KSPolySign
