-- Prove2me | Theorems.Thm_NKtLB_lemma_45
-- name    : NKtLB.lemma_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:14:47.57142+00:00
-- url     : https://prove2.me/theorems/d1db49c3-6f49-4c1e-829b-825e54f21bc0
-- title:
--   Lemma 45 — eliminating an $\mathsf{NTIME}\cap\mathsf{coNTIME}$ oracle from nK (corrected: $T(\ell)>0$)
-- statement:
--   There is a constant $c>0$ such that the following holds. Let $T:\mathbb N\to\mathbb N$ be time-constructible and non-decreasing with $T(n)\ge n$, and let $L\in\mathsf{NTIME}[T(n)]\cap\mathsf{coNTIME}[T(n)]$. Then for all sufficiently large $t$ and all strings $x,y$:
--
--   1. $\mathrm{nK}^{t\cdot T(t)\cdot\log^c(T(t))}(x\mid y)\le\mathrm{nK}^{t,L}(x\mid y)+c\log\log t$;
--   2. for every query-length bound $\ell$ with $T(\ell)>0$,
--   $$
--   \mathrm{nK}^{t\cdot T(\ell)\cdot\log^c(T(\ell)\cdot t)}(x\mid y)\ \le\ \mathrm{nK}^{t,L^{\le\ell}}(x\mid y)+c\log\log t .
--   $$
--
--   Access to an oracle in $\mathsf{NTIME}\cap\mathsf{coNTIME}$ can thus be removed from a nondeterministic description, at the price of a multiplicative time overhead $T$ and $O(\log\log t)$ bits. Lemma 105 and Eq. (30) both use this.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - reading: $c$ independent of $L$; "sufficiently large $t$" after $x,y$ and $\ell$ → $c$ before $T,L$; one threshold $t_0$ after $L$, uniform in $x,y,\ell$; reason: footnote 17: the exponent comes only from the universal machine, the $L$-dependent constants are absorbed once $t$ is large; the uniform threshold is the stronger reading
--   - correction: every $\ell\in\mathbb N$ → $\ell$ with $T(\ell)>0$; reason: false for $T(0)=0$, $\ell=0$: e.g. $T(n)=n$, $L=\emptyset$, $x=y=\varepsilon$; the left side is $\mathrm{nK}^0=\infty$ (a valid universal machine does not halt at step 0), the right side is finite for large $t$
--   - encoding: $\log^c(\cdot)$ in a time bound; "$L^{\le\ell}$" → $\lceil(\log_2\cdot)^c\rceil$; oracle $L$ with queries of length at most $\ell$; reason: time bounds are natural numbers; Def. 99 defines $O^{\le l}$ by the query lengths
--   - reading: $\mathsf{NTIME}[2^{\varepsilon n}]$ → time $c\lceil2^{\varepsilon n}\rceil+c$ for some $c$ (`NTIME (expBound ε)`); reason: the standard class with $O(T)$ time; the larger class makes the lower bound stronger
--   - encoding: complexities with $\min\emptyset=\infty$ → values in $\mathbb N\cup\{\infty\}$ compared in `EReal`; reason: $\infty\pm a=\infty$ for real $a$ matches the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 45, p.30 (proof pp.30–31, footnote 17)

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_nKtime
import Definitions.Def_NKtLB_NTIME
import Definitions.Def_NKtLB_coNTIME
import Definitions.Def_NKtLB_IsTimeConstructible
import Definitions.Def_NKtLB_toEReal

namespace NKtLB

/-- **Lemma 45 (eliminating an `NTIME[T] ∩ coNTIME[T]` oracle from `nK`)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 45, p.30),
**corrected: `T(ℓ) > 0` in the second bound**: "There is a constant `c > 0` such that the following
holds. For any time-constructible, non-decreasing `T : ℕ → ℕ`, `T(n) ≥ n` and every
`L ∈ NTIME[T(n)] ∩ coNTIME[T(n)]`, `x, y ∈ {0,1}^*`, and sufficiently large `t ∈ ℕ`,
`nK^{t·T(t)·log^c(T(t))}(x | y) ≤ nK^{t,L}(x | y) + c · log log t`. Specifically, restricting
query length to at most `ℓ ∈ ℕ`, for every `x, y ∈ {0,1}^*` and sufficiently large `t ∈ ℕ`,
`nK^{t·T(ℓ)·log^c(T(ℓ)·t)}(x | y) ≤ nK^{t,L^{≤ℓ}}(x | y) + c · log log t`."

**Formalization Note.** `c` depends only on `U` (footnote 17: "the exponent `c` comes only from the
universal machine's simulation overhead and is independent of `L`"); the threshold `t₀` depends on
`T` and `L` and is uniform in `x, y` and `ℓ`. Time bounds are rounded up: `log^c(·)` is
`⌈(log₂ ·)^c⌉`. `L^{≤ℓ}` means oracle `L` with queries of length at most `ℓ`. The hypothesis
`0 < T ℓ` is a correction: `T(n) ≥ n` allows `T(0) = 0`, and then for `ℓ = 0` the left side is
`nK^0 = ∞` (a valid universal machine does not halt at step `0`), while the right side is finite
for large `t` (e.g. `T(n) = n`, `L = ∅`, `x = y = ε`). -/
theorem lemma_45 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ → ℕ, IsTimeConstructible T → Monotone T → (∀ n, n ≤ T n) →
      ∀ L : Set (List Bool), L ∈ NTIME T → L ∈ coNTIME T →
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        (∀ x y : List Bool,
          toEReal (nKtime U ∅ ⊤ (t * T t * ⌈(Real.logb 2 (T t)) ^ c⌉₊) x y []) ≤
            toEReal (nKtime U L ⊤ t x y []) + ((c * Real.logb 2 (Real.logb 2 t) : ℝ) : EReal)) ∧
        (∀ ℓ : ℕ, 0 < T ℓ → ∀ x y : List Bool,
          toEReal (nKtime U ∅ ⊤ (t * T ℓ * ⌈(Real.logb 2 ((T ℓ : ℝ) * t)) ^ c⌉₊) x y []) ≤
            toEReal (nKtime U L ℓ t x y []) + ((c * Real.logb 2 (Real.logb 2 t) : ℝ) : EReal)) := by sorry

end NKtLB
