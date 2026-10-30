-- Prove2me | Theorems.Thm_KUModComp_composite_degree_lt
-- name    : KUModComp.composite_degree_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:00:49.860302+00:00
-- url     : https://prove2.me/theorems/ed640bf3-24d9-428a-922c-5c434ecc040b
-- title:
--   $f'(g_{0,0},\dots,g_{m-1,\ell-1})$ has degree less than $N' = Nm\ell d_0$ (corrected: $m \ge 1$)
-- statement:
--   Let $R$ be a commutative ring, $2 \le d_0 < d$, $\ell = \lceil \log_{d_0} d \rceil$, $m \ge 1$, $N \ge 1$. Let $f \in R[X_0,\dots,X_{m-1}]$ have individual degrees at most $d-1$, let $g_0,\dots,g_{m-1}, h \in R[X]$ have degree at most $N-1$, the leading coefficient of $h$ a unit, and $g_{i,j} = g_i^{d_0^{\,j}} \bmod h$. With $f' = \psi_{d_0,\ell}(f)$,
--   $$
--   \deg f'\bigl(g_{0,0}(X),\dots,g_{m-1,\ell-1}(X)\bigr) < N' = N m \ell d_0 .
--   $$
--   This is why $N'$ evaluation points suffice for the interpolation in step 5 of the proof of Theorem 3.1.
--
--   Differences from the source:
--   - correction: the parenthetical "degree less than $N'$" for all $m$ → assumes $m \ge 1$; reason: for $m = 0$, $N' = 0$, and $R = \mathbb Z$, $f = 1$, any $d > d_0 \ge 2$, $N \ge 1$, $h = 1$ satisfy every assumption, but $f'() = 1$ has degree $0 \not< 0$.
--   - encoding: degree at most $N - 1$ → `natDegree ≤ N - 1` with $N \ge 1$, degree in `WithBot ℕ`; reason: a polynomial with unit leading coefficient has degree $\ge 0$, so the source's $N$ is $\ge 1$; the zero polynomial has degree $\bot$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), proof of Theorem 3.1, step 5, p. 10

import Mathlib
import Definitions.Def_KUModComp_psi
import Definitions.Def_KUModComp_modCompSpec

open Polynomial

namespace KUModComp

/-- **The interpolated polynomial has degree less than `N'`** (Kedlaya–Umans, Dagstuhl 08381
(2008), proof of Theorem 3.1, step 5, p. 10; corrected: `m ≥ 1`). Let `2 ≤ d_0 < d`,
`ℓ = ⌈log_{d_0} d⌉`, `m ≥ 1`, `N ≥ 1`, `f ∈ R[X_0, …, X_{m-1}]` with individual degrees at most
`d - 1`, `g_0, …, g_{m-1}, h ∈ R[X]` of degree at most `N - 1`, the leading coefficient of `h` a
unit `u`, and `g_{i,j} = g_i^{d_0^j} mod h`. Then `f'(g_{0,0}, …, g_{m-1,ℓ-1})`, with
`f' = ψ_{d_0,ℓ}(f)`, is a univariate polynomial of degree less than `N' = N m ℓ d_0`.
(For `m = 0` the printed claim is false: `N' = 0` and `f = 1` gives degree `0`.) -/
theorem composite_degree_lt {R : Type*} [CommRing R] {m : ℕ} (d d₀ N : ℕ) (hd₀ : 2 ≤ d₀)
    (hd : d₀ < d) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (f : MvPolynomial (Fin m) R) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (g : Fin m → R[X]) (hg : ∀ i, (g i).natDegree ≤ N - 1)
    (hp : R[X]) (hpN : hp.natDegree ≤ N - 1) (u : Rˣ) (hu : hp.leadingCoeff = (u : R)) :
    (MvPolynomial.aeval
        (fun p : Fin m × Fin (Nat.clog d₀ d) => modU (g p.1 ^ (d₀ ^ (p.2 : ℕ))) hp u)
        (psi d₀ (Nat.clog d₀ d) f)).degree < ((N * m * Nat.clog d₀ d * d₀ : ℕ) : WithBot ℕ) := by sorry

end KUModComp
