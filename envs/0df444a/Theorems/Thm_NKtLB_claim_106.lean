-- Prove2me | Theorems.Thm_NKtLB_claim_106
-- name    : NKtLB.claim_106
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:17:38.729193+00:00
-- url     : https://prove2.me/theorems/62ac8054-de10-4cf7-b9a9-a8b53e48b49a
-- title:
--   Claim 106 — a guessed string of high nKt derandomizes $\mathrm{rK}^L$
-- statement:
--   This is the setting of the proof of Lemma 105. Let $\varepsilon,\gamma\in(0,1)$ and let $L$ be a language with
--   1. $L\in\mathsf{NTIME}[2^{\varepsilon n}]\cap\mathsf{coNTIME}[2^{\varepsilon n}]$,
--   2. $\mathrm{nKt}(x)\ge\gamma|x|$ for every $x\in L$,
--   3. $L\cap\{0,1\}^n\ne\emptyset$ for every $n\in\mathbb N$.
--   Let $n,m$ be large enough, $l,t,r\in\mathbb N$, $x\in\{0,1\}^n$, $y\in\{0,1\}^m$. Let $M$ be the program of $\mathrm{rK}^{(t;r),L^{\le l}}(x\mid y)$: a shortest program with queries of length at most $l$ and
--   $$
--   \Pr_{w\sim U_r}\bigl[M^{L^{\le l}}(y,w)=x\text{ in }t\text{ steps}\bigr]\ge\tfrac23 .
--   $$
--   Let $n'=C_1(n+m+l+r+\lceil\log t\rceil+\lceil1/\gamma\rceil)$, $N'=\lceil n'/\gamma\rceil$, and let $G:\{0,1\}^{N'}\times\{0,1\}^d\to\{0,1\}^r$ be the generator of Lemma 31 with $\varepsilon=1/6$. If $C_1$ is a large enough constant, then for every $s\in\{0,1\}^{N'}$ with $\mathrm{nKt}(s)\ge n'$,
--   $$
--   \Pr_{z\sim U_d}\bigl[M^{L^{\le l}}(y,G(s,z))=x\text{ in }t\text{ steps}\bigr]>\frac12 .
--   $$
--
--   So a string of high nKt complexity, which the nondeterministic description can guess and certify by membership in $L$, serves as a hard seed for derandomization.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead). The generators are those of any family $F$ with the properties of Lemma 31 (`IsReconstructivePRG c F`).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - generalization: "the PRG of Lemma 31" → every family F with `IsReconstructivePRG c F`; reason: the proof uses only the properties listed in Lemma 31; the paper's generator is such a family
--   - reading: "$C_1$ some large enough constant"; "large enough $n,m$" → $C_1\ge C_1^0$ with $C_1^0$ before $\varepsilon,\gamma,L$; a threshold $N_0$ after $L$; reason: the order of Lemma 105, whose constant $C$ precedes $\varepsilon,\gamma,L$ and is a function of $C_1$
--   - reading: "$M$ the program of $\mathrm{rK}^{(t;r),L^{\le l}}(x\mid y)$" → $|M|=\mathrm{rK}^{(t;r),L^{\le l}}(x\mid y)$ and $M$ qualifies (query bound, success $\ge2/3$); reason: the proof uses $|M|=\mathrm{rK}$; for an arbitrary long qualifying $M$ the claim fails (hard-wire $s$ and fail on $G(s,\cdot)$)
--   - reading: $\mathsf{NTIME}[2^{\varepsilon n}]$ → time $c\lceil2^{\varepsilon n}\rceil+c$ for some $c$ (`NTIME (expBound ε)`); reason: the standard class with $O(T)$ time; the larger class makes the lower bound stronger
--   - encoding: $R_{\mathrm{nKt}[s]}$ for $s:\mathbb N\to\mathbb N$ → $s:\mathbb N\to\mathbb R$; reason: the paper uses $s(n)=\gamma n$; integer-valued $s$ give the paper's set
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Claim 106, p.72 (setting of Lemma 105)

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_IsReconstructivePRG
import Definitions.Def_NKtLB_rK
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_NTIME
import Definitions.Def_NKtLB_coNTIME
import Definitions.Def_NKtLB_expBound
import Definitions.Def_NKtLB_RnKt

namespace NKtLB

/-- **Claim 106 (a guessed string of high `nKt` derandomizes `rK^L`)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Claim 106, p.72), in
the setting of the proof of Lemma 105: "Let `n′ = C₁(n + m + l + r + ⌈log t⌉ + ⌈1/γ⌉)`, where `C₁` is
some constant whose value will be determined later, and let `N′ = ⌈n′/γ⌉`. Let
`G : {0,1}^{N′} × {0,1}^d → {0,1}^r` be the pseudorandom generator of Lemma 31, with `ε = 1/6`. Let
`M^{(-)}` be the program of `rK^{(t;r),L^{≤l}}(x | y)`, such that `Pr_{w∼U_r}[M^{L^{≤l}}(y, w) = x in t
steps] ≥ 2/3`. … Claim 106. If `C₁` is some large enough constant, then for any `s ∈ {0,1}^{N′}`
satisfying `nKt(s) ≥ n′`, it holds that `Pr_{z∼U_d}[M^{L^{≤l}}(y, G(s, z)) = x in t steps] > 1/2`."

The setting of Lemma 105: `ε, γ ∈ (0, 1)`, `L ∈ NTIME[2^{εn}] ∩ coNTIME[2^{εn}]`, `nKt(x) ≥ γ|x|`
for all `x ∈ L`, and `L ∩ {0,1}^n ≠ ∅` for every `n`; `n, m` large enough, `x ∈ {0,1}^n`,
`y ∈ {0,1}^m`.

**Formalization Note.** "The program of `rK`" is a program `M` of length exactly
`rK^{(t;r),L^{≤l}}(x | y)` that qualifies (query bound on every `w`, success at least `2/3`); for
an arbitrary long qualifying program the claim fails (a program can hard-wire one `s` and fail
exactly on `G(s, ·)`). `G = F.G N′ r 6`. "`C₁` large enough" is `C₁ ≥ C₁₀` with `C₁₀` before
`ε, γ, L`, and "large enough `n, m`" is a threshold `N₀` after `L`, as in Lemma 105. -/
theorem claim_106 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code)
    (c : ℕ) (F : PRGFamily) (hF : IsReconstructivePRG c F) :
    ∃ C₁₀ : ℕ, ∀ C₁ : ℕ, C₁₀ ≤ C₁ → ∀ ε γ : ℝ, 0 < ε → ε < 1 → 0 < γ → γ < 1 →
      ∀ L : Set (List Bool), L ∈ NTIME (expBound ε) → L ∈ coNTIME (expBound ε) →
        L ⊆ RnKt U (fun k => γ * k) →
        (∀ n : ℕ, ∃ x ∈ L, x.length = n) →
      ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m → ∀ (l t r : ℕ) (x y : List Bool),
        x.length = n → y.length = m →
        ∀ M : List Bool, (M.length : ℕ∞) = rK U L l t r (2 / 3) x y →
          (∀ w : List Bool, w.length = r → U.QueryBounded L l ⟨M, y, [], w⟩ t) →
          (2 / 3 : ℝ) ≤ prob r (fun w => U.HaltsWith L ⟨M, y, [], w⟩ t (bitsSym x)) →
        ∀ n' N' : ℕ, n' = C₁ * (n + m + l + r + Nat.clog 2 t + ⌈1 / γ⌉₊) →
          N' = ⌈(n' : ℝ) / γ⌉₊ →
        ∀ s : List Bool, s.length = N' → (n' : ℕ∞) ≤ nKt U ∅ ⊤ s [] [] →
          (1 / 2 : ℝ) < prob (F.d N' r 6)
            (fun z => U.HaltsWith L ⟨M, y, [], F.G N' r 6 s z⟩ t (bitsSym x)) := by sorry

end NKtLB
