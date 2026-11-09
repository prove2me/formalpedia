-- Prove2me | Theorems.Thm_NKtLB_lemma_107
-- name    : NKtLB.lemma_107
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:16:30.664207+00:00
-- url     : https://prove2.me/theorems/a769a90f-e39d-4c6e-8984-1d36fc228c8a
-- title:
--   Lemma 107 — the SoI-type inequality for a dense language in $R_{\mathrm{nKt}}[\gamma n]$
-- statement:
--   There is a constant $C\in\mathbb N$ such that the following holds. Let $\varepsilon,\gamma\in(0,1)$, $b\in\mathbb N$, and let $L$ be a language with
--   1. $L\in\mathsf{NTIME}[2^{\varepsilon n}]\cap\mathsf{coNTIME}[2^{\varepsilon n}]$,
--   2. $\mathrm{nKt}(x)\ge\gamma|x|$ for every $x\in L$,
--   3. $|L\cap\{0,1\}^n|\ge2^n/n^b$ for every $n\in\mathbb N$.
--
--   Let $x,y$ be strings, $n_1=|x|$, $n_2=|y|$, $n=n_1+n_2$, and let $m_1,m_2\in\mathbb N$ with $m_1+m_2>0$ satisfy
--   $$
--   m_1\le\mathrm{nKt}(x\mid y)-C\Bigl(\frac{\varepsilon(n+1/\gamma)}{\gamma}+\log^3\frac{n^b}{\gamma}\Bigr),\qquad m_2\le\mathrm{nKt}(y)-C\Bigl(\frac{\varepsilon(n+1/\gamma)}{\gamma}+\log^3\frac{n^b}{\gamma}\Bigr).
--   $$
--   Let $G_1:\{0,1\}^{n_1}\times\{0,1\}^{d_1}\to\{0,1\}^{m_1}$ and $G_2:\{0,1\}^{n_2}\times\{0,1\}^{d_2}\to\{0,1\}^{m_2}$ be the generators of Lemma 31 with distinguishing parameter $1/2n^b$. Then there are $z_1\in\{0,1\}^{d_1}$ and $z_2\in\{0,1\}^{d_2}$ with
--   $$
--   G_1(x,z_1)\circ G_2(y,z_2)\in L .
--   $$
--
--   This is the step that drives Algorithm 1: from strings of conditional complexity $m_1$ and $m_2$ it produces a string of $L$ of length $m_1+m_2$.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead). The generators are those of any family $F$ with the properties of Lemma 31 (`IsReconstructivePRG c F`).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - generalization: "the PRG of Lemma 31" → every family F with `IsReconstructivePRG c F`; reason: the proof uses only the properties listed in Lemma 31; the paper's generator is such a family
--   - encoding: all strings $x,y$ → $n^b>0$; reason: excludes only $n=0<b$, where the parameter $1/2n^b$ and $\log(n^b/\gamma)$ are undefined
--   - reading: any $m_1,m_2\in\mathbb N$ → $m_1+m_2>0$; reason: at $m_1=m_2=0$ the conclusion is $\varepsilon\in L$, while property 3 at length $0$ ($|L\cap\{\varepsilon\}|\ge2^0/0^b$) is undefined for $b\ge1$; reading it as no constraint (Lean: $0$) and keeping $m_1=m_2=0$ would make $L\setminus\{\varepsilon\}$ a counterexample for every $L$ with properties 1–3 and small $\varepsilon/\gamma$, i.e. the item would assert that no such $L$ exists (open for $\gamma\le1/2$, §12.5); the proof uses property 3 only at the length $m_1+m_2$ of the generated string
--   - encoding: $O(f)$, $\mathrm{poly}(f)$ → $C f+C$, $\lceil C f^C\rceil+C$ with $C$ quantified before the data; reason: standard meaning; constants are chosen in the order the statement reads
--   - reading: $\mathsf{NTIME}[2^{\varepsilon n}]$ → time $c\lceil2^{\varepsilon n}\rceil+c$ for some $c$ (`NTIME (expBound ε)`); reason: the standard class with $O(T)$ time; the larger class makes the lower bound stronger
--   - encoding: $R_{\mathrm{nKt}[s]}$ for $s:\mathbb N\to\mathbb N$ → $s:\mathbb N\to\mathbb R$; reason: the paper uses $s(n)=\gamma n$; integer-valued $s$ give the paper's set
--   - encoding: complexities with $\min\emptyset=\infty$ → values in $\mathbb N\cup\{\infty\}$ compared in `EReal`; reason: $\infty\pm a=\infty$ for real $a$ matches the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 107, pp.73–74

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_IsReconstructivePRG
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_NTIME
import Definitions.Def_NKtLB_coNTIME
import Definitions.Def_NKtLB_expBound
import Definitions.Def_NKtLB_RnKt
import Definitions.Def_NKtLB_toEReal

namespace NKtLB

/-- **Lemma 107** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 107, pp.73–74): "There exists some constant `C ∈ ℕ` such that the
following holds. Suppose there exists `ε, γ ∈ (0, 1)` and `b ∈ ℕ` such that a language `L` satisfies
the following three properties: 1. `L ∈ NTIME[2^{εn}] ∩ coNTIME[2^{εn}]`, 2. `∀x ∈ L, nKt(x) ≥ γ·|x|`,
3. `∀n ∈ ℕ, |L ∩ {0,1}^n| ≥ 2^n/n^b`. For any strings `x, y ∈ {0,1}^*`, let `n₁ = |x|`, `n₂ = |y|`, and
`n = n₁ + n₂`. Consider any `m₁, m₂ ∈ ℕ` satisfying
`m₁ ≤ nKt(x | y) − C · (ε · (n + 1/γ)/γ + log³(n^b/γ))`,
`m₂ ≤ nKt(y) − C · (ε · (n + 1/γ)/γ + log³(n^b/γ))`. We define `G₁, G₂` to be the PRG of Lemma 31,
with distinguishing parameter `1/2n^b`: `G₁ : {0,1}^{n₁} × {0,1}^{d₁} → {0,1}^{m₁}`,
`G₂ : {0,1}^{n₂} × {0,1}^{d₂} → {0,1}^{m₂}`. Then there exists `z₁ ∈ {0,1}^{d₁}`,
`z₂ ∈ {0,1}^{d₂}` such that `G₁(x, z₁) ◦ G₂(y, z₂) ∈ L`."

**Formalization Note.** `G_i = F.G n_i m_i (2n^b)` for a family with `IsReconstructivePRG c F`;
`C` comes after `U, F` and before `ε, γ, b, L`. `0 < n^b` excludes only `n = 0 < b`, where the
parameter `1/2n^b` and `log(n^b/γ)` are undefined. `0 < m₁ + m₂` excludes the case whose conclusion
is `ε ∈ L`: property 3 at length `0` reads `|L ∩ {ε}| ≥ 2^0/0^b`, undefined for `b ≥ 1` (and `0` in
Lean), so it does not give `ε ∈ L`. Without it the statement would turn every `L` with properties
1–3 and small `ε/γ` into a counterexample (`L ∖ {ε}` keeps the properties; take incompressible
`x, y` and `m₁ = m₂ = 0`), i.e. it would assert that no such `L` exists, which for `γ ≤ 1/2` is open
(§12.5, p.77). -/
theorem lemma_107 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code)
    (c : ℕ) (F : PRGFamily) (hF : IsReconstructivePRG c F) :
    ∃ C : ℕ, ∀ ε γ : ℝ, 0 < ε → ε < 1 → 0 < γ → γ < 1 → ∀ (b : ℕ) (L : Set (List Bool)),
      L ∈ NTIME (expBound ε) → L ∈ coNTIME (expBound ε) →
        L ⊆ RnKt U (fun k => γ * k) →
        (∀ n : ℕ, (2 : ℝ) ^ n / (n : ℝ) ^ b ≤ (Set.ncard (L ∩ {x : List Bool | x.length = n}) : ℝ)) →
      ∀ (x y : List Bool) (n₁ n₂ n : ℕ), x.length = n₁ → y.length = n₂ → n = n₁ + n₂ →
        0 < n ^ b → ∀ m₁ m₂ : ℕ, 0 < m₁ + m₂ →
        ((m₁ : ℝ) : EReal) ≤ toEReal (nKt U ∅ ⊤ x y []) -
          ((C * (ε * (n + 1 / γ) / γ + (Real.logb 2 ((n : ℝ) ^ b / γ)) ^ 3) : ℝ) : EReal) →
        ((m₂ : ℝ) : EReal) ≤ toEReal (nKt U ∅ ⊤ y [] []) -
          ((C * (ε * (n + 1 / γ) / γ + (Real.logb 2 ((n : ℝ) ^ b / γ)) ^ 3) : ℝ) : EReal) →
        ∃ z₁ z₂ : List Bool, z₁.length = F.d n₁ m₁ (2 * n ^ b) ∧ z₂.length = F.d n₂ m₂ (2 * n ^ b) ∧
          F.G n₁ m₁ (2 * n ^ b) x z₁ ++ F.G n₂ m₂ (2 * n ^ b) y z₂ ∈ L := by sorry

end NKtLB
