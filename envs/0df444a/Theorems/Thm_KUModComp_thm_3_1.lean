-- Prove2me | Theorems.Thm_KUModComp_thm_3_1
-- name    : KUModComp.thm_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:02:14.183373+00:00
-- url     : https://prove2.me/theorems/67f1a882-82d5-4ee1-83d0-437724b4fbb5
-- title:
--   Theorem 3.1: MODULAR COMPOSITION reduces to one MULTIVARIATE MULTIPOINT EVALUATION
-- statement:
--   **Theorem 3.1.** There are absolute constants $C, k \in \mathbb N$ and one family of straight-line programs $A(d, d_0, m, N, n)$, built from these natural numbers alone, with the following property. Let $2 \le d_0 < d$, $m \in \mathbb N$, and $n + 1 \le N$; put
--   $$
--   \ell = \lceil \log_{d_0} d \rceil, \qquad N' = N m \ell d_0 .
--   $$
--   1. **Cost.** $A(d,d_0,m,N,n)$ uses at most
--   $$
--   C\,(d^m + mN)\,d_0\,\bigl(\log_2(d^m + mN) + 1\bigr)^k
--   $$
--   ring operations.
--   2. **Oracle.** It makes exactly one invocation of MULTIVARIATE MULTIPOINT EVALUATION, with parameters $d_0$, $m' = \ell m$, $N'$.
--   3. **Correctness.** For every commutative ring $R$, every input $f \in R[X_0,\dots,X_{m-1}]$ with individual degrees at most $d-1$, $g_0,\dots,g_{m-1} \in R[X]$ of degree at most $N-1$, $h \in R[X]$ of degree $n$ whose leading coefficient is a unit, and every $N'$ distinct elements $\beta_0,\dots,\beta_{N'-1}$ of $R$ whose differences are units, the program, run on $(f, g, h, \beta)$, outputs the coefficients of
--   $$
--   f(g_0(X),\dots,g_{m-1}(X)) \bmod h(X).
--   $$
--
--   So MODULAR COMPOSITION costs $O((d^m + mN)d_0)\cdot\mathrm{poly}\log(d^m+mN)$ ring operations plus one call to multivariate multipoint evaluation with $d_0$, $\ell m$, $N'$: a fast algorithm for the latter gives one for the former. This is the reduction on which the paper's fast modular composition and polynomial factorization rest.
--
--   Differences from the source:
--   - reading: "ring operations" → instructions `zero`, `one`, `add`, `neg`, `mul`, `inv` of a straight-line program, with no comparison or branch on ring values, and `inv` relied on only for units (correctness holds for every inversion primitive $\iota$ that inverts units); reason: the algebraic model of the paper, which inverts only units (the leading coefficient of $h$, the differences of the $\beta$'s).
--   - reading: polynomials "represented explicitly by a list of their coefficients" → the input list `layout f g h β` ($d^m$ coefficients of $f$, $N$ of each $g_i$, $n+1$ of $h$, the $N'$ points), with $\deg h = n$ part of the input; reason: $h$ is given with its degree so that its leading coefficient is known, as the source's unit hypothesis presupposes.
--   - reading: $O((d^m+mN)d_0)\cdot\mathrm{poly}\log(d^m+mN)$ → $\le C(d^m+mN)d_0(\log_2(d^m+mN)+1)^k$ with $C, k$ absolute; reason: standard meaning of $O(\cdot)\cdot\mathrm{polylog}$; the $+1$ keeps the bound meaningful at $d^m + mN = 1$ ($m = 0$).
--   - reading: "plus one invocation of MULTIVARIATE MULTIPOINT EVALUATION with parameters $d_0, m', N'$" → the oracle-call log equals exactly $[(d_0, \ell m, N')]$, the oracle's arguments being free register references; reason: the source charges the invocation as a unit, separately from the ring operations.
--   - generalization: for fixed $R$ and each $d_0$ an algorithm → one program family $A$, depending only on $(d, d_0, m, N, n)$, correct over every commutative ring; reason: specializes to the source's statement for each $R$ and $d_0$.
--   - encoding: $\ell = \lceil \log_{d_0} d \rceil$ → `Nat.clog d₀ d`; $f \bmod h$ → remainder by the monic associate (`modCompSpec`); exponent vectors of $f$ indexed by `finFunctionFinEquiv`; $R$ in `Type`; reason: Lean conventions, same instances.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Theorem 3.1, p. 9 (proof pp. 9–10)

import Mathlib
import Definitions.Def_KUModComp_mmeSpec
import Definitions.Def_KUModComp_modCompSpec
import Definitions.Def_KUModComp_SLP

namespace KUModComp

/-- **Theorem 3.1** (Kedlaya–Umans, *Fast polynomial factorization and modular composition*,
Dagstuhl Seminar Proceedings 08381 (2008), p. 9): MODULAR COMPOSITION reduces to one invocation of
MULTIVARIATE MULTIPOINT EVALUATION.

There are absolute constants `C, k` and one family of straight-line programs `A d d₀ m N n`,
generated from the natural-number parameters alone, such that for all `2 ≤ d₀ < d`, all `m`, and
all `n + 1 ≤ N` (`n = deg h ≤ N - 1`), with `ℓ = ⌈log_{d₀} d⌉ = Nat.clog d₀ d` and
`N' = N m ℓ d₀`:
1. `A` uses at most `C (d^m + mN) d₀ (log₂(d^m + mN) + 1)^k` ring operations;
2. `A` makes exactly one call to MULTIVARIATE MULTIPOINT EVALUATION, with parameters
   `(d₀, ℓ m, N')`;
3. over every commutative ring `R`, for every inversion primitive `ι` that inverts units, every
   input `f` (individual degrees `≤ d - 1`), `g_0, …, g_{m-1}` (degree `≤ N - 1`), `h` (degree `n`,
   leading coefficient the unit `u`), and every `N'` distinct points `β` whose pairwise differences
   are units, the program run on `layout f g h β` outputs the `n` coefficients of
   `f(g_0, …, g_{m-1}) mod h`. -/
theorem thm_3_1 :
    ∃ (C k : ℕ) (A : ℕ → ℕ → ℕ → ℕ → ℕ → SLP), ∀ d d₀ m N n : ℕ, 2 ≤ d₀ → d₀ < d → n + 1 ≤ N →
      ringOps (A d d₀ m N n) ≤
          C * (d ^ m + m * N) * d₀ * (Nat.log 2 (d ^ m + m * N) + 1) ^ k ∧
        oracleCalls (A d d₀ m N n) =
          [(d₀, Nat.clog d₀ d * m, N * m * Nat.clog d₀ d * d₀)] ∧
        ∀ (R : Type) [CommRing R] (ι : R → R), (∀ x : Rˣ, ι (x : R) = ((x⁻¹ : Rˣ) : R)) →
          ∀ (f : (Fin m → Fin d) → R) (g : Fin m → Fin N → R) (h : Fin (n + 1) → R) (u : Rˣ)
            (β : Fin (N * m * Nat.clog d₀ d * d₀) → R),
            (u : R) = h (Fin.last n) → Function.Injective β →
            (∀ i j, i ≠ j → IsUnit (β i - β j)) →
            run ι (A d d₀ m N n) (layout f g h β) = List.ofFn (modCompSpec f g h u) := by sorry

end KUModComp
