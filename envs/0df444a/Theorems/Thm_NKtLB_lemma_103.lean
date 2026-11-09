-- Prove2me | Theorems.Thm_NKtLB_lemma_103
-- name    : NKtLB.lemma_103
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:14:43.823207+00:00
-- url     : https://prove2.me/theorems/30a4e961-485b-4f92-abe2-704440c29c67
-- title:
--   Lemma 103 — reconstruction from oracle access to a dense language (corrected: for all sufficiently large $n$ and $m_1+m_2>0$)
-- statement:
--   There exist constants $C\in\mathbb N$ and $N_0$ such that the following holds. Let $b\in\mathbb N$ and let $L$ be a language with $|L\cap\{0,1\}^n|\ge 2^n/n^b$ for every $n$. Let $x,y$ be strings, $n_1=|x|$, $n_2=|y|$, and $n=n_1+n_2\ge N_0$. Let $m_1,m_2\in\mathbb N$ with $m_1+m_2>0$ satisfy
--   $$
--   m_1\le\mathrm{rK}^{(n^{C b};\,C n),L^{\le3n}}(x\mid y)-C\log^3(n^b),\qquad m_2\le\mathrm{rK}^{(n^{C b};\,C n),L^{\le3n}}(y)-C\log^3(n^b),
--   $$
--   and let $G_1:\{0,1\}^{n_1}\times\{0,1\}^{d_1}\to\{0,1\}^{m_1}$ and $G_2:\{0,1\}^{n_2}\times\{0,1\}^{d_2}\to\{0,1\}^{m_2}$ be the generators of Lemma 31 with parameter $\varepsilon=1/2n^b$. Then there are $z_1\in\{0,1\}^{d_1}$ and $z_2\in\{0,1\}^{d_2}$ with
--   $$
--   G_1(x,z_1)\circ G_2(y,z_2)\in L .
--   $$
--
--   So a dense language cannot avoid all pseudorandom concatenations built from strings of high conditional complexity. This is the reconstruction half of Lemma 107.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead). The generators are those of any family $F$ with the properties of Lemma 31 (`IsReconstructivePRG c F`).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - generalization: "the PRG of Lemma 31" → every family F with `IsReconstructivePRG c F`; reason: the proof uses only the properties listed in Lemma 31; the paper's generator is such a family
--   - correction: for all strings $x,y$ → $n=|x|+|y|\ge N_0$; reason: false at $n=1$: the time bound $n^{Cb}$ is $1$, so for a valid universal machine whose first step never halts (one exists whenever a valid one does) both rK values are $\infty$ and $m_1$ is unconstrained; $G_1(x,\cdot)$ has at most $2^{d_1}$ values with $d_1\le2c$ independent of $m_1$, and all strings except these values form an $L$ with $b=1$ once $m_1\ge2c+2$, on which the conclusion fails
--   - correction: any $m_1,m_2\in\mathbb N$ → $m_1+m_2>0$; reason: at $m_1=m_2=0$ the conclusion is $\varepsilon\in L$, but the density bound $2^0/0^b$ at length $0$ is undefined for $b\ge1$ (and $0$ in Lean), so nothing forces $\varepsilon\in L$; counterexample: $b=1$, $L=\{0,1\}^*\setminus\{\varepsilon\}$, any large $n$, $x,y$ with $\mathrm{rK}(x\mid y)\ge|x|$ and $\mathrm{rK}(y)\ge|y|$ (counting), $m_1=m_2=0$
--   - encoding: $O(f)$, $\mathrm{poly}(f)$ → $C f+C$, $\lceil C f^C\rceil+C$ with $C$ quantified before the data; reason: standard meaning; constants are chosen in the order the statement reads
--   - encoding: complexities with $\min\emptyset=\infty$ → values in $\mathbb N\cup\{\infty\}$ compared in `EReal`; reason: $\infty\pm a=\infty$ for real $a$ matches the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 103, p.70

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_IsReconstructivePRG
import Definitions.Def_NKtLB_rK
import Definitions.Def_NKtLB_toEReal

namespace NKtLB

/-- **Lemma 103 (reconstruction from oracle access to a dense language)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 103, p.70),
**corrected: for all sufficiently large `n`**: "There exists some constant `C ∈ ℕ` such that the
following holds. For any `b ∈ ℕ` and any language `L` satisfying `|L ∩ {0,1}^n| ≥ 2^n/n^b` and any
strings `x, y ∈ {0,1}^*`, let `n₁ = |x|` and `n₂ = |y|`, and `n = n₁ + n₂`. Then for any
`m₁, m₂ ∈ ℕ` satisfying `m₁ ≤ rK^{(n^{C·b};C·n),L^{≤3n}}(x | y) − C · log³(n^b)`,
`m₂ ≤ rK^{(n^{C·b};C·n),L^{≤3n}}(y) − C · log³(n^b)`, we define `G₁, G₂` to be the PRG of Lemma 31,
with parameter `ε = 1/2n^b`: `G₁ : {0,1}^{n₁} × {0,1}^{d₁} → {0,1}^{m₁}`,
`G₂ : {0,1}^{n₂} × {0,1}^{d₂} → {0,1}^{m₂}`. Then there exists `z₁ ∈ {0,1}^{d₁}`,
`z₂ ∈ {0,1}^{d₂}` such that `G₁(x, z₁) ◦ G₂(y, z₂) ∈ L`."

**Formalization Note.** The density hypothesis holds at every length. `G_i = F.G n_i m_i (2n^b)`
for a family with `IsReconstructivePRG c F`. `rK` is `⊤` when no program qualifies, and then the
hypothesis on `m_i` holds for every `m_i`. The added threshold `N₀ ≤ n` is a correction: at `n = 1`
the time bound `n^{C·b}` is `1`, so for a valid universal machine whose first step never halts both
`rK` values are `∞` and `m₁` is unconstrained, while `G₁(x, ·)` has at most `2^{d₁}` values with
`d₁ ≤ c·log³ 2 + c` independent of `m₁`; the language of all strings except these values is dense
with `b = 1` once `m₁ ≥ 2c + 2`, and the conclusion fails. The added hypothesis `0 < m₁ + m₂` is
a second correction: the density bound `2^0/0^b` at length `0` is undefined in the paper for
`b ≥ 1` (and `0` in Lean), so nothing forces `ε ∈ L`, while at `m₁ = m₂ = 0` the conclusion says
exactly `ε ∈ L`. For `b = 1`, `L = {0,1}^* ∖ {ε}`, any large `n` and `x, y` with
`rK(x | y) ≥ |x|`, `rK(y) ≥ |y|` (counting), `m₁ = m₂ = 0` meets every hypothesis and the conclusion
fails. -/
theorem lemma_103 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code)
    (c : ℕ) (F : PRGFamily) (hF : IsReconstructivePRG c F) :
    ∃ C N₀ : ℕ, ∀ (b : ℕ) (L : Set (List Bool)),
      (∀ n : ℕ, (2 : ℝ) ^ n / (n : ℝ) ^ b ≤ (Set.ncard (L ∩ {x : List Bool | x.length = n}) : ℝ)) →
      ∀ (x y : List Bool) (n₁ n₂ n : ℕ), x.length = n₁ → y.length = n₂ → n = n₁ + n₂ → N₀ ≤ n →
      ∀ m₁ m₂ : ℕ, 0 < m₁ + m₂ →
        ((m₁ : ℝ) : EReal) ≤ toEReal (rK U L (3 * n) (n ^ (C * b)) (C * n) (2 / 3) x y) -
          ((C * (Real.logb 2 ((n : ℝ) ^ b)) ^ 3 : ℝ) : EReal) →
        ((m₂ : ℝ) : EReal) ≤ toEReal (rK U L (3 * n) (n ^ (C * b)) (C * n) (2 / 3) y []) -
          ((C * (Real.logb 2 ((n : ℝ) ^ b)) ^ 3 : ℝ) : EReal) →
        ∃ z₁ z₂ : List Bool, z₁.length = F.d n₁ m₁ (2 * n ^ b) ∧ z₂.length = F.d n₂ m₂ (2 * n ^ b) ∧
          F.G n₁ m₁ (2 * n ^ b) x z₁ ++ F.G n₂ m₂ (2 * n ^ b) y z₂ ∈ L := by sorry

end NKtLB
