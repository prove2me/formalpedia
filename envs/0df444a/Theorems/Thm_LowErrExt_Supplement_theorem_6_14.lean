-- Prove2me | Theorems.Thm_LowErrExt_Supplement_theorem_6_14
-- name    : LowErrExt.Supplement.theorem_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:37:34.620889+00:00
-- url     : https://prove2.me/theorems/817b8c75-f482-4d1b-a531-172518d745a6
-- title:
--   Theorem 6.14 — spreadness implies rapid mixing: $H_2[2^{t-1}X-2^{t-1}X]\ge k_t$
-- statement:
--   Let $m\ge2$. There are constants $C,c>0$ and $c'\in(0,1)$ depending only on $m$ such that the following holds. Let $G$ be a finite abelian group with torsion $m$, let $V\subseteq G$ be a coset with $n=H_0[V]$, and let $\mathbf X\sim V$ be $(r,k)_2$-spread in $V$ with $n\ge r$ and $k\ge C$. Let $\tau$ be the largest integer with $r+\frac{(1+c)^\tau-1}{c}\,k\le n$, and $\tau'$ the largest integer with $(1-c')^{\tau'-1-\tau}\big(n-(r-k)-(1+c)^\tau k\big)\ge C$. Then
--   $$H_2\big[2^{t-1}\mathbf X-2^{t-1}\mathbf X\big]\ge k_t:=\begin{cases}(1+c)^t\,k, & 0\le t\le\tau,\\ n-(r-k)-(1-c')^{t-\tau}\big(n-(r-k)-(1+c)^\tau k\big), & \tau<t\le\tau'.\end{cases}$$
--
--   The collision entropy of the iterated differences grows geometrically until the scale of the spreadness is used up, and then the remaining gap shrinks geometrically: a step-by-step form of spreadness implies rapid mixing.
--
--   **Formalization Note** Spreadness is the published `IsSpread2`; $\tau$ is characterized by $r+g(\tau)k\le n<r+g(\tau+1)k$ with $g(t)=((1+c)^t-1)/c$, and $t\le\tau'$ for $t>\tau$ by $(1-c')^{t-1-\tau}(n-(r-k)-(1+c)^\tau k)\ge C$, exactly as in the published Theorem 6.32.
--
--   Differences from the source:
--   - encoding: τ the largest integer with r + ((1+c)^τ − 1)/c·k ≤ n; τ′ the largest integer with (1 − c′)^{τ′−1−τ}·A ≥ C, A = n − (r − k) − (1 + c)^τ k → τ : ℕ with r + g(τ)k ≤ n < r + g(τ+1)k; for t > τ, the second bound is required exactly when (1 − c′)^{t−1−τ}·A ≥ C; reason: g is increasing (k ≥ C > 0) and τ ≥ 0 exists since n ≥ r; the left side of the τ′ condition decreases in t when A > 0, and when A ≤ 0 no τ′ exists and the condition fails, as in the published Theorem 6.32
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 6.14, p.42

import Mathlib
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_iterDiff
import Definitions.Def_LowErrExt_IsCoset
import Definitions.Def_LowErrExt_IsSpread

namespace LowErrExt.Supplement

open LowErrExt

/-- **Theorem 6.14 (Spreadness implies rapid mixing).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 6.14, p.42: "Let G be a finite abelian group with torsion m ≥ 2, and let V ⊆ G be a coset with
n := H0[V]. There exist constants C, c > 0 and c′ ∈ (0, 1) depending only on m such that the following
holds. If X ∼ V is (r, k)₂-spread in V, and n ≥ r and k ≥ C, then H2[2^{t−1}X − 2^{t−1}X] ≥ k_t :=
(1 + c)^t · k if 0 ≤ t ≤ τ, and n − (r − k) − (1 − c′)^{t−τ} · (n − (r − k) − (1 + c)^τ · k) if
τ < t ≤ τ′, where τ is the largest integer such that r + ((1+c)^τ − 1)/c · k ≤ n, and τ′ is the largest
integer such that (1 − c′)^{τ′−1−τ} · (n − (r − k) − (1 + c)^τ · k) ≥ C."

**Formalization Note.** Same encoding of `τ`, `τ′` as the published Theorem 6.32: `τ ∈ ℕ` is
characterized by `r + g(τ)k ≤ n < r + g(τ+1)k` with `g(t) = ((1+c)^t − 1)/c` (increasing, `k ≥ C > 0`,
and `τ ≥ 0` exists since `n ≥ r`); for `t > τ`, `t ≤ τ′` iff `(1 − c′)^{t−1−τ} · A ≥ C` with
`A = n − (r − k) − (1 + c)^τ k` (the left side decreases in `t` when `A > 0`; for `A ≤ 0` there is no
`τ′` and the inequality fails too). `t = 0` is `X` itself (`½X − ½X := X`). Spreadness is the
published `IsSpread2` (which includes `supp X ⊆ V`); `H2`, `H0` are published. -/
theorem theorem_6_14 (m : ℕ) (hm : 2 ≤ m) :
    ∃ C c c' : ℝ, 0 < C ∧ 0 < c ∧ 0 < c' ∧ c' < 1 ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G], (∀ x : G, m • x = 0) →
        ∀ (V : Set G) (X : PMF G) (r k : ℝ), IsCoset V → IsSpread2 r k V X →
          r ≤ H0 V → C ≤ k →
            ∀ τ : ℕ, r + ((1 + c) ^ τ - 1) / c * k ≤ H0 V →
              H0 V < r + ((1 + c) ^ (τ + 1) - 1) / c * k →
                (∀ t : ℕ, t ≤ τ → (1 + c) ^ t * k ≤ H2 (iterDiff t X)) ∧
                (∀ t : ℕ, τ < t →
                  C ≤ (1 - c') ^ (t - 1 - τ) * (H0 V - (r - k) - (1 + c) ^ τ * k) →
                    H0 V - (r - k) - (1 - c') ^ (t - τ) * (H0 V - (r - k) - (1 + c) ^ τ * k) ≤
                      H2 (iterDiff t X)) := by sorry

end LowErrExt.Supplement
