-- Prove2me | Theorems.Thm_NKtLB_corollary_104
-- name    : NKtLB.corollary_104
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:15:54.095067+00:00
-- url     : https://prove2.me/theorems/e3f9962d-2557-4485-bf66-011a6257c87a
-- title:
--   Corollary 104 — an rK upper bound from a distinguisher
-- statement:
--   Let $G$ be the generator of Lemma 31. There are constants $C$ and $N_0$ such that the following holds for all $n,m\ge N_0$ with $m\le2^n$ and every $\varepsilon\in(0,1)$. Let $x\in\{0,1\}^n$, let $O$ be an oracle, let $l,n',t\in\mathbb N$ and $y\in\{0,1\}^{n'}$, and let $B^{(-)}:\{0,1\}^m\times\{0,1\}^{n'}\times\{0,1\}^{r'}\to\{0,1\}$ be an algorithm running in time $t$ with queries to $O$ of length at most $l$. If
--   $$
--   \Pr_{z\sim U_d,\,w'\sim U_{r'}}\bigl[B^{O^{\le l}}(G(x;z),y,w')=1\bigr]-\Pr_{w\sim U_m,\,w'\sim U_{r'}}\bigl[B^{O^{\le l}}(w,y,w')=1\bigr]\ \ge\ 2\varepsilon,
--   $$
--   then
--   $$
--   \mathrm{rK}^{(\mathrm{poly}(n t/\varepsilon);\,O(r'+m)),O^{\le l}}(x\mid y)\ \le\ m+|B|+O(\log^3(n/\varepsilon)),
--   $$
--   where $|B|$ is the description length of $B$.
--
--   This is the form in which Lemma 31 is applied: an efficient distinguisher gives a short randomized description of the seed $x$.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead). The generators are those of any family $F$ with the properties of Lemma 31 (`IsReconstructivePRG c F`).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - generalization: "the PRG of Lemma 31" → every family F with `IsReconstructivePRG c F`; reason: the proof uses only the properties listed in Lemma 31; the paper's generator is such a family
--   - encoding: algorithm $B$ with $|B|$ its description length → a program $B$ run by $U$ on auxiliary $\langle s,y\rangle$ and randomness $w'$, halting within $t$ steps with output $0$ or $1$ on every $s,w'$; reason: the paper's algorithms are programs of $U$; $G$ is taken at $k=\lceil1/\varepsilon\rceil$
--   - encoding: $O(f)$, $\mathrm{poly}(f)$ → $C f+C$, $\lceil C f^C\rceil+C$ with $C$ quantified before the data; reason: standard meaning; constants are chosen in the order the statement reads
--   - encoding: complexities with $\min\emptyset=\infty$ → values in $\mathbb N\cup\{\infty\}$ compared in `EReal`; reason: $\infty\pm a=\infty$ for real $a$ matches the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Corollary 104, p.70

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_IsReconstructivePRG
import Definitions.Def_NKtLB_rK
import Definitions.Def_NKtLB_toEReal

namespace NKtLB

/-- **Corollary 104 (an `rK` upper bound from a distinguisher)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Corollary 104, p.70): "For
sufficiently large `n, m ∈ ℕ` such that `m ≤ 2^n`, and any `ε ∈ (0, 1)`, let `G` be the generator
of Lemma 31. Consider any string `x ∈ {0,1}^n`, oracle `O`, parameters `l, n′, t ∈ ℕ`, string
`y ∈ {0,1}^{n′}`, and algorithm `B^{(-)} : {0,1}^m × {0,1}^{n′} × {0,1}^{r′} → {0,1}` running in time
`t`. If it holds that `Pr_{z∼U_d, w′∼U_{r′}}[B^{O^{≤l}}(G(x; z), y, w′) = 1] −
Pr_{w∼U_m, w′∼U_{r′}}[B^{O^{≤l}}(w, y, w′) = 1] ≥ 2ε`, then we have
`rK^{(poly(n·t/ε);O(r′+m)),O^{≤l}}(x | y) ≤ m + |B| + O(log³(n/ε))`, where `|B|` is the description
length of `B`."

**Formalization Note.** `G` is `F.G n m k` with `k = ⌈1/ε⌉` for a family `F` satisfying
`IsReconstructivePRG c F`. `B` is a program run by `U` with `(s, y)` (encoded by `tupleEnc`) on the
auxiliary tape and `w′` on the randomness tape, oracle `O` with queries of length at most `l`;
"running in time `t`" is: on every `s ∈ {0,1}^m`, `w′ ∈ {0,1}^{r′}` it halts within `t` steps with
output `0` or `1`. "`= 1`" is output `1`. `poly(n·t/ε)` is `⌈C·(n·t/ε)^C⌉ + C`, `O(r′+m)` is
`C·(r′+m) + C`, `O(log³(n/ε))` is `C·log₂³(n/ε) + C`; `C` and the threshold `N₀` come after `U, F`
and before all data. -/
theorem corollary_104 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code)
    (c : ℕ) (F : PRGFamily) (hF : IsReconstructivePRG c F) :
    ∃ C N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m → m ≤ 2 ^ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ x : List Bool, x.length = n → ∀ (O : Set (List Bool)) (l n' t : ℕ) (y : List Bool),
      y.length = n' → ∀ (r' : ℕ) (B : List Bool),
        (∀ s w' : List Bool, s.length = m → w'.length = r' →
          U.QueryBounded O l ⟨B, tupleEnc [s, y], [], w'⟩ t ∧
          (U.HaltsWith O ⟨B, tupleEnc [s, y], [], w'⟩ t [Sym.zero] ∨
            U.HaltsWith O ⟨B, tupleEnc [s, y], [], w'⟩ t [Sym.one])) →
        2 * ε ≤ prob (F.d n m ⌈1 / ε⌉₊ + r') (fun v =>
            U.HaltsWith O ⟨B, tupleEnc [F.G n m ⌈1 / ε⌉₊ x (v.take (F.d n m ⌈1 / ε⌉₊)), y], [],
              v.drop (F.d n m ⌈1 / ε⌉₊)⟩ t [Sym.one]) -
          prob (m + r') (fun v =>
            U.HaltsWith O ⟨B, tupleEnc [v.take m, y], [], v.drop m⟩ t [Sym.one]) →
        toEReal (rK U O l (⌈(C : ℝ) * ((n : ℝ) * t / ε) ^ C⌉₊ + C) (C * (r' + m) + C) (2 / 3) x y) ≤
          ((m + B.length + C * (Real.logb 2 ((n : ℝ) / ε)) ^ 3 + C : ℝ) : EReal) := by sorry

end NKtLB
