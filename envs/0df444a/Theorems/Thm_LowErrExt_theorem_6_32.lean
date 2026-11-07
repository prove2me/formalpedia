-- Prove2me | Theorems.Thm_LowErrExt_theorem_6_32
-- name    : LowErrExt.theorem_6_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:25.934424+00:00
-- url     : https://prove2.me/theorems/9887122c-1d25-4405-9ccf-e797655e9e2e
-- title:
--   Theorem 6.32 — growth of spreadness under iterated differences
-- statement:
--   Let $m\ge2$. There are constants $C,c>0$ and $c'\in(0,1)$ depending only on $m$ such that the following holds. Let $G$ be a finite abelian group with torsion $m$, $V\subseteq G$ a coset with $n:=H_0[V]$, and $\mathbf X$ a source that is $(r,k)_2$-spread in $V$ with $k\ge C$. Let $n'\in[r,n]$, write $g(t)=((1+c)^t-1)/c$, let $\tau$ be the largest integer with $r+g(\tau)k\le n'$, let
--   $$A:=n'-(r-k)-(1+c)^{\tau}k,$$
--   and let $\tau'$ be the largest integer with $(1-c')^{\tau'-1-\tau}A\ge C$. Then $2^{t-1}\mathbf X-2^{t-1}\mathbf X$ is $(r_t,k_t)_2$-spread in $2^{t-1}V-2^{t-1}V$, where
--   $$(r_t,k_t)=\begin{cases}\big(r+g(t)\,k,\ (1+c)^t k\big) & 0\le t\le\tau,\\[2pt] \big(n',\ n'-(r-k)-(1-c')^{t-\tau}A\big) & \tau<t\le\tau'.\end{cases}$$
--
--   Spreadness grows geometrically until resolution $n'$ is reached, after which the entropy gap at resolution $n'$ shrinks geometrically.
--
--   Differences from the source:
--   - encoding: G has torsion m → m • x = 0 for every x ∈ G; reason: the paper's meaning of bounded torsion (footnote 20, p.40); same instances
--   - encoding: spreadness over all homomorphisms L out of G (Definition 6.2) → spreadness over the quotient maps G → G/K for subgroups K (IsSpread); reason: a homomorphism with kernel K is an injective map after π_K, so images and entropies agree (Observation 6.5's argument); same instances
--   - encoding: τ, τ′ the largest integers with the stated inequalities → τ ∈ ℕ given by r + g(τ)k ≤ n′ < r + g(τ+1)k; for t > τ, t ≤ τ′ written as (1 − c′)^{t−1−τ}·A ≥ C; reason: g is increasing and k > 0, so this τ is the largest; the left side decreases in t when A > 0, and when A ≤ 0 no τ′ exists and both readings give an empty range
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 6.32, pp.47–48

import Mathlib
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_iterDiff
import Definitions.Def_LowErrExt_IsCoset
import Definitions.Def_LowErrExt_IsSpread

namespace LowErrExt

/-- **Theorem 6.32 (Growth of Spreadness).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 6.32, pp.47–48: "Let G be a finite abelian group with torsion m ≥ 2, and let V ⊆ G be a coset
with n := H0[V]. There exist constants C, c > 0 and c′ ∈ (0, 1) depending only on m such that the
following holds. If X ∼ V is (r, k)2-spread in V, and k ≥ C, then for any n′ ∈ [r, n], it holds that
2^{t−1}X − 2^{t−1}X is (rt, kt)2-spread in 2^{t−1}V − 2^{t−1}V for (rt, kt) :=
(r + ((1+c)^t − 1)/c · k, (1 + c)^t · k) if 0 ≤ t ≤ τ, and
(n′, n′ − (r − k) − (1 − c′)^{t−τ} · (n′ − (r − k) − (1 + c)^τ · k)) if τ < t ≤ τ′, where τ is the
largest integer such that r + ((1+c)^τ − 1)/c · k ≤ n′, and τ′ is the largest integer such that
(1 − c′)^{τ′−1−τ} · (n′ − (r − k) − (1 + c)^τ · k) ≥ C."

**Formalization Note.** `τ ∈ ℕ` is characterized by `r + g(τ)k ≤ n′ < r + g(τ+1)k` with
`g(t) = ((1+c)^t − 1)/c`, which is the largest such integer since `g` is increasing and `k ≥ C > 0`
(and `τ ≥ 0` since `n′ ≥ r`). For `t > τ`, `t ≤ τ′` holds iff
`(1 − c′)^{t−1−τ} · A ≥ C` with `A = n′ − (r − k) − (1 + c)^τ k`, because the left side decreases in
`t` when `A > 0`; when `A ≤ 0` no `τ′` exists and the second range is empty, which the inequality
also gives. `t = 0` is `X` itself (`½X − ½X := X`). -/
theorem theorem_6_32 (m : ℕ) (hm : 2 ≤ m) :
    ∃ C c c' : ℝ, 0 < C ∧ 0 < c ∧ 0 < c' ∧ c' < 1 ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G], (∀ x : G, m • x = 0) →
        ∀ (V : Set G) (X : PMF G) (r k : ℝ), IsCoset V → IsSpread2 r k V X → C ≤ k →
          ∀ n' : ℝ, r ≤ n' → n' ≤ H0 V →
            ∀ τ : ℕ, r + ((1 + c) ^ τ - 1) / c * k ≤ n' →
              n' < r + ((1 + c) ^ (τ + 1) - 1) / c * k →
                (∀ t : ℕ, t ≤ τ →
                  IsSpread2 (r + ((1 + c) ^ t - 1) / c * k) ((1 + c) ^ t * k)
                    (iterDiffSet t V) (iterDiff t X)) ∧
                (∀ t : ℕ, τ < t →
                  C ≤ (1 - c') ^ (t - 1 - τ) * (n' - (r - k) - (1 + c) ^ τ * k) →
                    IsSpread2 n'
                      (n' - (r - k) - (1 - c') ^ (t - τ) * (n' - (r - k) - (1 + c) ^ τ * k))
                      (iterDiffSet t V) (iterDiff t X)) := by sorry

end LowErrExt
