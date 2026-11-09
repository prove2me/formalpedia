-- Prove2me | Theorems.Thm_NKtLB_eq_30
-- name    : NKtLB.eq_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:16:42.066443+00:00
-- url     : https://prove2.me/theorems/9c609bca-fccc-4bf9-8e82-3ddc9569ba1a
-- title:
--   Eq. (30) — the output of Algorithm 1 has $\mathrm{nKt}\le n+5\varepsilon n+O(\log^3n+\log\log\frac1{\gamma-1/2})$
-- statement:
--   This is the setting of the proof of Theorem 8. Let $\gamma\in(1/2,1)$, $b\in\mathbb N$, $\gamma'=(\gamma+1/2)/2$, and let $L$ be a language with
--   1. $L\in\mathsf{NTIME}[2^{\varepsilon n}]\cap\mathsf{coNTIME}[2^{\varepsilon n}]$,
--   2. $\mathrm{nKt}(x)\ge\gamma|x|$ for every $x\in L$,
--   3. $|L\cap\{0,1\}^n|\ge2^n/n^b$ for all sufficiently large $n$.
--
--   Let $s_i$ and $\theta_i$ be the strings and thresholds of Algorithm 1 run on $(\gamma,1^n)$ with oracle $L$.
--   There is a constant $C$ (depending on $b$) such that, for all large enough $n$, if Algorithm 1 on $(\gamma,1^n)$ with oracle $L$ outputs a string $s_{i_0}$, then
--   $$
--   \mathrm{nKt}(s_{i_0})\ \le\ n+5\varepsilon n+C\Bigl(\log^3n+\log\log\frac1{\gamma-1/2}\Bigr).
--   $$
--
--   The output has a short description: the algorithm runs in time $2^{n+O(\log^3n)}$ with queries of length at most $5n$, and Lemma 45 removes the oracle. Compared with Claim 108, this upper bound contradicts $\mathrm{nKt}(s_{i_0})\ge n/(2-2\gamma')$ when $\varepsilon$ is small.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead). The generators are those of any family $F$ with the properties of Lemma 31 (`IsReconstructivePRG c F`).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - generalization: "the PRG of Lemma 31" → every family F with `IsReconstructivePRG c F`; reason: the proof uses only the properties listed in Lemma 31; the paper's generator is such a family
--   - reading: $O(\cdot)$ in a proof that fixes $\gamma$ and $b$ (p.74) → $C$ after $b$, before $\gamma,\varepsilon,L$; "large $n$" after $L$; reason: the explicit $\log\log(1/(\gamma-1/2))$ term carries the $\gamma$-dependence; the seed lengths are $O(b^3\log^3n)$, so $C$ depends on $b$
--   - reading: $\mathsf{NTIME}[2^{\varepsilon n}]$ → time $c\lceil2^{\varepsilon n}\rceil+c$ for some $c$ (`NTIME (expBound ε)`); reason: the standard class with $O(T)$ time; the larger class makes the lower bound stronger
--   - encoding: $R_{\mathrm{nKt}[s]}$ for $s:\mathbb N\to\mathbb N$ → $s:\mathbb N\to\mathbb R$; reason: the paper uses $s(n)=\gamma n$; integer-valued $s$ give the paper's set
--   - encoding: complexities with $\min\emptyset=\infty$ → values in $\mathbb N\cup\{\infty\}$ compared in `EReal`; reason: $\infty\pm a=\infty$ for real $a$ matches the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Eqs. (29)–(30), p.76

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_IsReconstructivePRG
import Definitions.Def_NKtLB_alg1Out
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_NTIME
import Definitions.Def_NKtLB_coNTIME
import Definitions.Def_NKtLB_expBound
import Definitions.Def_NKtLB_RnKt
import Definitions.Def_NKtLB_toEReal

namespace NKtLB

/-- **Equation (30): the output of Algorithm 1 has small `nKt`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Eqs. (29)–(30), p.76):
"`nKt(s_{i₀}) ≤ nK^{t₁}(s_{i₀}) + log t₁ ≤ K^{t₀,L^{≤5n}}(s_{i₀}) + n + 5εn + O(log³ n + log i₀)
≤ n + 5εn + O(log³ n + log i₀ + log log(1/(γ − 1/2)))` (by Equation (29))
`≤ n + 5εn + O(log³ n + log log(1/(γ − 1/2)))`, (30)".

In the setting of the proof of Theorem 8 (p.74; see `claim_108`), for all large enough `n`, if
Algorithm 1 run on `(γ, 1^n)` with oracle `L` outputs a string `s` (`s = s_{i₀}`), then
`nKt(s) ≤ n + 5εn + C · (log³ n + log log(1/(γ − 1/2)))`.

**Formalization Note.** The output of Algorithm 1 is `alg1Out` (the first `i₀ ≥ 2` with
`θ_{i₀} > n/(2 − 2γ′)`). The constant `C` of the `O(·)` depends on `U`, on the family `F` and on
`b` (fixed at the start of the proof, p.74; the seed lengths of Algorithm 1 are `O(b³ log³ n)`), and
comes before `γ`, `ε` and `L`; "large enough `n`" comes after `L`. -/
theorem eq_30 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code)
    (c : ℕ) (F : PRGFamily) (hF : IsReconstructivePRG c F) :
    ∀ b : ℕ, ∃ C : ℝ, ∀ γ : ℝ, 1 / 2 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ L : Set (List Bool), L ∈ NTIME (expBound ε) → L ∈ coNTIME (expBound ε) →
        L ⊆ RnKt U (fun k => γ * k) →
        (∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ^ n / (n : ℝ) ^ b ≤ (Set.ncard (L ∩ {x : List Bool | x.length = n}) : ℝ)) →
      ∀ᶠ n : ℕ in Filter.atTop, ∀ s : List Bool, alg1Out F L γ b n = some s →
        toEReal (nKt U ∅ ⊤ s [] []) ≤
          ((n + 5 * ε * n + C * ((Real.logb 2 n) ^ 3 +
            Real.logb 2 (Real.logb 2 (1 / (γ - 1 / 2)))) : ℝ) : EReal) := by sorry

end NKtLB
