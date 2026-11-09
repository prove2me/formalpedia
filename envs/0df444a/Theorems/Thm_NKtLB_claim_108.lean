-- Prove2me | Theorems.Thm_NKtLB_claim_108
-- name    : NKtLB.claim_108
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:16:26.730358+00:00
-- url     : https://prove2.me/theorems/0e313946-0876-44ed-9cec-7ce754c912e0
-- title:
--   Claim 108 — Algorithm 1 stays in $L$ and terminates
-- statement:
--   This is the setting of the proof of Theorem 8. Let $\gamma\in(1/2,1)$, $b\in\mathbb N$, $\gamma'=(\gamma+1/2)/2$, and let $L$ be a language with
--   1. $L\in\mathsf{NTIME}[2^{\varepsilon n}]\cap\mathsf{coNTIME}[2^{\varepsilon n}]$,
--   2. $\mathrm{nKt}(x)\ge\gamma|x|$ for every $x\in L$,
--   3. $|L\cap\{0,1\}^n|\ge2^n/n^b$ for all sufficiently large $n$.
--
--   Let $s_i$ and $\theta_i$ be the strings and thresholds of Algorithm 1 run on $(\gamma,1^n)$ with oracle $L$.
--   For a fixed $\gamma$, if $\varepsilon$ is small enough, then for all large enough $n$ there is an integer
--   $$
--   i_0\ \le\ \log_{\gamma'}\Bigl(1-\frac1{2\gamma'}\Bigr)+2
--   $$
--   such that
--   1. $s_i\in L$ for every $1\le i\le i_0$, and
--   2. $\theta_{i_0}>n/(2-2\gamma')$.
--
--   So Algorithm 1 produces, within boundedly many rounds, a string of $L$ whose length forces $\mathrm{nKt}\ge n/(2-2\gamma')>n$. This is the core of the contradiction in the proof of Theorem 8.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead). The generators are those of any family $F$ with the properties of Lemma 31 (`IsReconstructivePRG c F`).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - generalization: "the PRG of Lemma 31" → every family F with `IsReconstructivePRG c F`; reason: the proof uses only the properties listed in Lemma 31; the paper's generator is such a family
--   - reading: "if $\varepsilon$ is small enough, then for all large enough $n$" → $\varepsilon<\varepsilon_0(\gamma)$ with $\varepsilon_0$ before $b,L$; eventually in $n$, after $L$; reason: the proof takes $\varepsilon<(\gamma-\gamma')/20C$ with $C$ of Lemma 107, depending only on $\gamma$
--   - reading: $\mathsf{NTIME}[2^{\varepsilon n}]$ → time $c\lceil2^{\varepsilon n}\rceil+c$ for some $c$ (`NTIME (expBound ε)`); reason: the standard class with $O(T)$ time; the larger class makes the lower bound stronger
--   - encoding: $R_{\mathrm{nKt}[s]}$ for $s:\mathbb N\to\mathbb N$ → $s:\mathbb N\to\mathbb R$; reason: the paper uses $s(n)=\gamma n$; integer-valued $s$ give the paper's set
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Claim 108, p.75 (proof pp.75–76; setting p.74)

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_IsReconstructivePRG
import Definitions.Def_NKtLB_alg1
import Definitions.Def_NKtLB_alg1Theta
import Definitions.Def_NKtLB_NTIME
import Definitions.Def_NKtLB_coNTIME
import Definitions.Def_NKtLB_expBound
import Definitions.Def_NKtLB_RnKt

namespace NKtLB

/-- **Claim 108 (Algorithm 1 stays in `L` and terminates)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Claim 108, p.75): "For a fixed
`γ`, if `ε` is small enough, then for all large enough `n`, there exists some integer
`i₀ ≤ log_{γ′}(1 − 1/(2γ′)) + 2` such that 1. For any `i ≤ i₀`, `s_i ∈ L`, and 2. `θ_{i₀} > n/(2 − 2γ′)`."

The setting is the proof of Theorem 8 (p.74): `γ ∈ (1/2, 1)`, `b ∈ ℕ`, `γ′ = (γ + 1/2)/2`, and `L`
with 1. `L ∈ NTIME[2^{εn}] ∩ coNTIME[2^{εn}]`, 2. `∀x ∈ L, nKt(x) ≥ γ·|x|`, 3. for all sufficiently
large `n ∈ ℕ`, `|L ∩ {0,1}^n| ≥ 2^n/n^b`; `s_i` and `θ_i` are those of Algorithm 1 (p.75) run with
oracle `L`.

**Formalization Note.** Algorithm 1 is `alg1`, `θ_i` is `alg1Theta`, with the generators of a
family `F` satisfying `IsReconstructivePRG c F`. "`ε` small enough" is `ε < ε₀(γ)` with `ε₀` before
`b` and `L`; "large enough `n`" is eventually in `n`, after `L`. `i` ranges over `1 ≤ i ≤ i₀`
(`s₀ = ⊥`). -/
theorem claim_108 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code)
    (c : ℕ) (F : PRGFamily) (hF : IsReconstructivePRG c F) :
    ∀ γ : ℝ, 1 / 2 < γ → γ < 1 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (b : ℕ) (L : Set (List Bool)), L ∈ NTIME (expBound ε) → L ∈ coNTIME (expBound ε) →
        L ⊆ RnKt U (fun k => γ * k) →
        (∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ^ n / (n : ℝ) ^ b ≤ (Set.ncard (L ∩ {x : List Bool | x.length = n}) : ℝ)) →
      ∀ᶠ n : ℕ in Filter.atTop, ∃ i₀ : ℕ,
        (i₀ : ℝ) ≤ Real.logb ((γ + 1 / 2) / 2) (1 - 1 / (2 * ((γ + 1 / 2) / 2))) + 2 ∧
        (∀ i : ℕ, 1 ≤ i → i ≤ i₀ → ∃ s : List Bool, alg1 F L γ b n i = some s ∧ s ∈ L) ∧
        (n : ℝ) / (2 - 2 * ((γ + 1 / 2) / 2)) < alg1Theta γ n i₀ := by sorry

end NKtLB
