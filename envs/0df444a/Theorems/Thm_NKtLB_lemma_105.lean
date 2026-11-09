-- Prove2me | Theorems.Thm_NKtLB_lemma_105
-- name    : NKtLB.lemma_105
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:16:02.385521+00:00
-- url     : https://prove2.me/theorems/94a3dd6a-67db-47be-abb0-18632be719aa
-- title:
--   Lemma 105 — derandomizing $\mathrm{rK}^L$
-- statement:
--   There is a constant $C$ such that the following holds. Let $\varepsilon,\gamma\in(0,1)$ and let $L$ be a language with
--   1. $L\in\mathsf{NTIME}[2^{\varepsilon n}]\cap\mathsf{coNTIME}[2^{\varepsilon n}]$,
--   2. $\mathrm{nKt}(x)\ge\gamma|x|$ for every $x\in L$,
--   3. $L\cap\{0,1\}^n\ne\emptyset$ for every $n\in\mathbb N$.
--   Then for all large enough $n,m\in\mathbb N$, all $l,t,r\in\mathbb N$ with $l,r\ge1$, and all $x\in\{0,1\}^n$, $y\in\{0,1\}^m$,
--   $$
--   \mathrm{nKt}(x\mid y)\ \le\ \mathrm{rK}^{(t;r),L^{\le l}}(x\mid y)+C\Bigl(\frac{\varepsilon(n+m+l+r+1/\gamma)}{\gamma}+\log^3\frac{nmlr}{\gamma}+\log t\Bigr).
--   $$
--
--   Membership in a language of high-complexity strings that is decidable in $\mathsf{NTIME}\cap\mathsf{coNTIME}[2^{\varepsilon n}]$ thus lets nondeterministic descriptions simulate randomized ones with oracle access to that language. This is the derandomization half of Lemma 107.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - reading: "there exists some constant $C$"; "for all large enough $n,m$" → $C$ before $\varepsilon,\gamma,L$; a threshold $N_0$ after $L$; reason: the order in which the lemma is stated
--   - encoding: any $l,r\in\mathbb N$ → $l,r\ge1$; reason: $\log^3(nmlr/\gamma)$ is undefined at $l=0$ or $r=0$
--   - reading: $\mathsf{NTIME}[2^{\varepsilon n}]$ → time $c\lceil2^{\varepsilon n}\rceil+c$ for some $c$ (`NTIME (expBound ε)`); reason: the standard class with $O(T)$ time; the larger class makes the lower bound stronger
--   - encoding: $R_{\mathrm{nKt}[s]}$ for $s:\mathbb N\to\mathbb N$ → $s:\mathbb N\to\mathbb R$; reason: the paper uses $s(n)=\gamma n$; integer-valued $s$ give the paper's set
--   - encoding: complexities with $\min\emptyset=\infty$ → values in $\mathbb N\cup\{\infty\}$ compared in `EReal`; reason: $\infty\pm a=\infty$ for real $a$ matches the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 105, p.72 (proof pp.72–73)

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_rK
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_NTIME
import Definitions.Def_NKtLB_coNTIME
import Definitions.Def_NKtLB_expBound
import Definitions.Def_NKtLB_RnKt

namespace NKtLB

/-- **Lemma 105 (derandomizing `rK^L`)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 105, p.72): "There exists some constant `C`
such that the following holds. If there exists `ε, γ ∈ (0, 1)` such that a language `L` satisfies
the following three properties: 1. `L ∈ NTIME[2^{εn}] ∩ coNTIME[2^{εn}]`, 2. `∀x ∈ L, nKt(x) ≥ γ·|x|`,
3. `∀n ∈ ℕ, L ∩ {0,1}^n ≠ ∅`, then for all large enough `n, m ∈ ℕ`, any `l, t, r ∈ ℕ` and any strings
`x ∈ {0,1}^n`, `y ∈ {0,1}^m`, we have
`nKt(x | y) ≤ rK^{(t;r),L^{≤l}}(x | y) + C · (ε · (n + m + l + r + 1/γ)/γ + log³(nmlr/γ) + log t)`."

**Formalization Note.** `C` depends only on `U` and comes before `ε, γ, L`; the threshold `N₀`
comes after `L`. `1 ≤ l` and `1 ≤ r` exclude `l = 0` and `r = 0`, where `log³(nmlr/γ)` is
undefined (`log 0`). Comparison in `EReal`; `rK = ∞` makes the bound trivial. -/
theorem lemma_105 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∃ C : ℝ, ∀ ε γ : ℝ, 0 < ε → ε < 1 → 0 < γ → γ < 1 →
      ∀ L : Set (List Bool), L ∈ NTIME (expBound ε) → L ∈ coNTIME (expBound ε) →
        L ⊆ RnKt U (fun k => γ * k) →
        (∀ n : ℕ, ∃ x ∈ L, x.length = n) →
      ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m → ∀ l t r : ℕ, 1 ≤ l → 1 ≤ r →
        ∀ x y : List Bool, x.length = n → y.length = m →
          toEReal (nKt U ∅ ⊤ x y []) ≤ toEReal (rK U L l t r (2 / 3) x y) +
            ((C * (ε * (n + m + l + r + 1 / γ) / γ +
              (Real.logb 2 ((n : ℝ) * m * l * r / γ)) ^ 3 + Real.logb 2 t) : ℝ) : EReal) := by sorry

end NKtLB
