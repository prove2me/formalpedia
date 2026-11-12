-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_lemma_5_16
-- name    : MultStretchAPASP.Weighted.lemma_5_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:10:59.131665+00:00
-- url     : https://prove2.me/theorems/5bfc1c0d-c3a2-4a14-bccb-c0fcc494054b
-- title:
--   Lemma 5.16 with Lemmas 5.4–5.5 — weighted 2-APASP in Õ(n^{2+a} + n^{a+ω(1−a,1,1−a)+o(1)} log² W_max) time w.h.p., hence Õ(n^{ω−(ω−2)²/(ω−1)+o(1)} log² W_max)
-- statement:
--   **Setting.** The input is a simple undirected graph $G$ on $n\ge1$ vertices with integer edge weights in $[W_{\max}]=\{1,\dots,W_{\max}\}$, $W_{\max}\ge1$ (no connectivity is assumed). A **2-APASP** output is a symmetric table $d$ with $\delta(u,v)\le d[u,v]\le2\delta(u,v)$ for all pairs, where $\delta$ is the shortest-path distance ($\infty$ for disconnected pairs). Programs run on the randomized word RAM; $\omega(\cdot,\cdot,\cdot)$ is the operational exponent of §2.4 on the same machine and $\omega=\omega(1,1,1)$. Write $L=\log_2(W_{\max}+1)+1$ for $\log W_{\max}$.
--
--   For a time bound $f(n,W_{\max})$, say that a program **solves 2-APASP in $\tilde O(f)$ w.h.p.** if for every $c>0$ there is a constant $C$ such that on every input (i) every run halts with a correct 2-APASP output, and (ii) with probability at least $1-n^{-c}$ the run halts within $C(\log_2(n+2))^C f(n,W_{\max})+C$ steps.
--
--   **Statement.** Lemma 5.16 together with the output specification of Algorithm 10 (Lemmas 5.4, 5.5):
--
--   1. for every $a\in[0,1]$ and $\eta>0$ there is a program solving 2-APASP in
--   $$\tilde O\bigl(n^{2+a}+n^{a+\omega(1-a,1,1-a)+\eta}\,L^2\bigr)\ \text{w.h.p.};$$
--   2. for every $\eta>0$ there is one in $\tilde O\bigl(n^{\omega-\frac{(\omega-2)^2}{\omega-1}+\eta}L^2\bigr)$ (the choice $a=\frac{\omega-2}{\omega-1}$);
--   3. if $a+\omega(1-a,1,1-a)\le2+\frac{(1-a)^2}{4}$ for all $a\in[0,\frac12]$ (the new rectangular bounds [4, 28]), there is one in $\tilde O(n^{2.17157288}L^2)$;
--   4. if $0.24186294+\omega(0.75813706,1,0.75813706)<2.24186294$ (the earlier bounds [3, 29]), there is one in $\tilde O(n^{2.24186294}L^2)$.
--
--   This is the paper's headline result: a stretch-2 APASP algorithm for integer weights whose exponent is below $\omega$ whenever $\omega>2$. By Dor, Halperin and Zwick, computing a $(2-\epsilon)$-APASP is at least as hard as Boolean matrix multiplication, so stretch 2 is the smallest multiplicative stretch an algorithm with exponent below $\omega$ can achieve.
--
--   Differences from the source:
--
--   - reading: an algorithm with a running time (the paper names no machine model) → a program of the published randomized word RAM DynConnWC.Program with the run notions of MinKCutII_Main_Runs, words of wordSize C inp T = C·⌈log₂(|inp| + Σ inp + 2 + ⌈T⌉)⌉ bits, input read once in order, output written as words; reason: a standard unit-cost word RAM with Θ(log)-bit words; the same machine defines ω(a, b, c), so the exponents in the bounds and the machine agree
--   - encoding: a weighted undirected graph G = (V, E) with positive integer weights in [W_max] ∪ {∞}, assuming |E| = O(n²) → a simple graph on Fin n (1 ≤ n) given as m edge records (u, v, c) with u ≠ v, no repeated pair and 1 ≤ c ≤ Wmax (1 ≤ Wmax), input words [n, Wmax, m, u₀, v₀, c₀, …]; reason: simple graphs have |E| ≤ n(n−1)/2; ∞ = no edge
--   - encoding: output: a symmetric table d with δ(u, v) ≤ d[u, v] ≤ 2δ(u, v) → the program writes D[u, v] row by row in the two-word code ([0, k] for k, [1, 0] for ∞), D symmetric with dist ≤ D ≤ 2·dist in ℝ≥0∞; reason: an unambiguous code for ∞; d[u, v] = ∞ exactly for disconnected pairs
--   - reading: Algorithm 10 outputs the table (Lemmas 5.4, 5.5 for every outcome of S₁) and runs in the stated time w.h.p. → on every random tape the run halts with a correct output; the tapes on which it does not halt within the bound have measure at most n^(−c); reason: correctness is proved for every outcome of the sampling, only the running time is random
--   - reading: with high probability (probability ≥ 1 − n^{−c} for any fixed c > 0, constants depending on c; p. 5) → for every c > 0 a constant C with failure measure (outer measure of the set of bad outcomes) at most n^(−c); reason: the paper's own definition of w.h.p.; the measure of the failure set avoids measurability side conditions
--   - reading: Õ(·) and the o(1) in the exponent → for every η > 0 one program, and for every c > 0 a constant C with time C·(log₂(n+2))^C·bound + C; reason: Õ hides polylog n (p. 5); ω is an infimum, so the program may depend on the slack η but not on the instance
--   - encoding: log W_max → log₂(W_max + 1) + 1; reason: equals log W_max up to a constant factor for W_max ≥ 2 and does not vanish at W_max = 1
--   - reading: q₁ = n^{−a} for some a ∈ [0, 1] (the runtime of Algorithm 10) → for every a ∈ [0, 1] and η > 0 a program achieving the bound; reason: the lemma is a running-time bound for the algorithm with that parameter; the existence of a program is what it asserts about the problem
--   - reading: ω(a, b, c) in the bounds → omega3 a b c, the operational exponent of §2.4 on the same word RAM with deterministic programs; ω = omega3 1 1 1; reason: the paper defines ω by running time (p. 7); deterministic because Theorem 2.14 claims a deterministic algorithm with time n^{ω(1,r,1)+o(1)}
--   - reading: using the new FMM bounds [4, 21, 28] gives Õ(n^{2.17157288} log² W_max) → if a + ω(1−a, 1, 1−a) ≤ 2 + (1−a)²/4 for all a ∈ [0, 1/2], then a program with bound n^{2.17157288}·L²; reason: the rectangular bounds are external; the hypothesis is the inequality the proof derives from them (p. 32), needed at a = 3 − 2√2 ∈ [0, 1/2]; 5 − 2√2 < 2.17157288, so no o(1) remains
--   - reading: using the previous FMM bounds [3, 13, 29], the runtime is Õ(n^{2.24186294} log² W_max) → if 0.24186294 + ω(0.75813706, 1, 0.75813706) < 2.24186294, then a program with bound n^{2.24186294}·L²; reason: the hypothesis is what the earlier bounds give at a = 0.24186294 (p. 32); strict, because the printed bound carries no o(1)
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 31, Lemma 5.16, with the output specification of Algorithm 10 (p. 21) proved as Lemmas 5.4 (p. 22) and 5.5 (p. 23)

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus
import Definitions.Def_MultStretchAPASP_Weighted_Encoding
import Definitions.Def_MultStretchAPASP_Weighted_OmegaExp

set_option autoImplicit false

open DynConnWC

namespace MultStretchAPASP.Weighted

/-- **Lemma 5.16** (p. 31) with the output specification of Algorithm 10 (p. 21; Lemmas 5.4,
5.5): weighted 2-APASP on the randomized word RAM. Every clause asserts a program that, on every
simple undirected graph with `n ≥ 1` vertices and integer weights in `[Wmax]`, always halts with
a symmetric table `d` satisfying `δ(u, v) ≤ d[u, v] ≤ 2δ(u, v)`, and halts within `Õ(bound)` steps
with probability at least `1 − n^{−c}` for every `c > 0` (`TwoAPASPWithin`), where
`L = log₂(Wmax + 1) + 1` stands for `log Wmax` and `η > 0` for the `o(1)`:

1. for every `a ∈ [0, 1]` (sampling rate `q₁ = n^{−a}`): `bound = n^{2+a} + n^{a+ω(1−a,1,1−a)+η}·L²`;
2. at `a = (ω − 2)/(ω − 1)`: `bound = n^{ω−(ω−2)²/(ω−1)+η}·L²`;
3. if the rectangular bounds of [4, 28] give `a + ω(1 − a, 1, 1 − a) ≤ 2 + (1 − a)²/4` for
   `a ∈ [0, 1/2]`: `bound = n^{2.17157288}·L²`;
4. if the earlier bounds of [3, 29] give `0.24186294 + ω(0.75813706, 1, 0.75813706) < 2.24186294`:
   `bound = n^{2.24186294}·L²`. -/
theorem lemma_5_16 :
    (∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ η : ℝ, 0 < η → ∃ P : Program, ∀ c : ℝ, 0 < c → ∃ C : ℕ,
      TwoAPASPWithin P C c fun n Wmax =>
        (n : ℝ) ^ (2 + a) + (n : ℝ) ^ (a + omega3 (1 - a) 1 (1 - a) + η) * logW Wmax ^ 2) ∧
    (∀ η : ℝ, 0 < η → ∃ P : Program, ∀ c : ℝ, 0 < c → ∃ C : ℕ,
      TwoAPASPWithin P C c fun n Wmax =>
        (n : ℝ) ^ (omega - (omega - 2) ^ 2 / (omega - 1) + η) * logW Wmax ^ 2) ∧
    ((∀ a : ℝ, 0 ≤ a → a ≤ 1 / 2 → a + omega3 (1 - a) 1 (1 - a) ≤ 2 + (1 - a) ^ 2 / 4) →
      ∃ P : Program, ∀ c : ℝ, 0 < c → ∃ C : ℕ,
        TwoAPASPWithin P C c fun n Wmax => (n : ℝ) ^ (2.17157288 : ℝ) * logW Wmax ^ 2) ∧
    ((0.24186294 : ℝ) + omega3 0.75813706 1 0.75813706 < 2.24186294 →
      ∃ P : Program, ∀ c : ℝ, 0 < c → ∃ C : ℕ,
        TwoAPASPWithin P C c fun n Wmax => (n : ℝ) ^ (2.24186294 : ℝ) * logW Wmax ^ 2) := by sorry

end MultStretchAPASP.Weighted
