-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_8_23
-- name    : MatMulDS.Supplement.theorem_8_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:23:19.091169+00:00
-- url     : https://prove2.me/theorems/b611eab6-c537-4935-8185-38fdda3cb247
-- title:
--   Theorem 8.23 — diameter, radius and eccentricities for $m\le n^{2-\gamma}$ in $O_\gamma(n^{2-\xi})$ w.h.p.
-- statement:
--   Let $\beta\le1/50$ be an admissible saving, fix $0<\gamma\le1$, and set $\xi=\gamma\beta/20$. Using the bounds (3.3) of [Uzn26], there is a randomized algorithm that, given a connected undirected unweighted graph $G=(V,E)$ with $n\ge2$ vertices and $m\le n^{2-\gamma}$ edges, returns, with high probability,
--
--   1. a $(3/2,7/2)$-approximation of $\operatorname{diam}(G)$,
--   2. a $(5/3,4)$-approximation of $e_G(v)$ for every $v\in V$, and
--   3. a vertex $z$ such that $e_G(z)$ is a $(3/2,5/2)$-approximation of $\operatorname{rad}(G)$,
--
--   and runs in $O_\gamma(n^{2-\xi})=O_\gamma(n^{2-0.0000133\gamma})$ time with high probability.
--
--   It gives these classical approximations in truly subquadratic time for every subquadratic number of edges.
--
--   Differences from the source:
--   - encoding: a randomized algorithm on the word RAM → a program of the mission's machine over $\mathbb F_2$, whose coin instruction draws a uniform bit, every step counted, every word size $w\ge K\lceil\log_2(n+1)\rceil+K$; reason: a word RAM with random bits; the field cells over $\mathbb F_2$ are a bit array
--   - reading: "with high probability" → for every $c>0$ a constant $C$ (depending on $c$) with probability at least $1-n^{-c}$; reason: the form the paper's own proofs give (Theorems E.4, E.5, Lemma J.2; SUPPLEMENT decision 1)
--   - reading: "Using the bounds (3.3) of [Uzn26]" → no hypothesis; reason: it names a cited theorem the proof uses; assuming it would weaken the statement (SUPPLEMENT decision 2)
--   - encoding: a graph $G=(V,E)$ with $n$ vertices and $m$ edges → $V=\{0,\dots,n-1\}$, any adjacency-list representation $L$ of $G$ as input words, $m$ the number of edges; reason: the source's input convention (§3: graphs given by adjacency lists)
--   - encoding: outputs → word cell $0$: the estimate of $\operatorname{diam}(G)$; cell $1+v$: of $e_G(v)$; cell $n+1$: the vertex $z$; integer estimates; reason: for an integer $x$ any real $\tilde x\in[x,\rho x+\sigma]$ rounds down to an integer in the same interval
--   - reading: "returns, with high probability, … and runs in … time with high probability" → one event: halting within $Cn^{2-\xi}$ steps with correct outputs, with probability at least $1-n^{-c}$; reason: the two events hold w.h.p. separately iff jointly (union bound)
--   - encoding: $O_\gamma$ → the program and all constants chosen after $\gamma$; reason: $\gamma$ is fixed in the statement
--   - encoding: the numerical form $O_\gamma(n^{2-0.0000133\gamma})$ → a separate conjunct, the inequality at $\beta=0.0002666$; reason: the source evaluates its bound at the admissible saving of Theorem 7.4
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 8.23, p.63 (PDF p.65); proof in App. J, pp.117–118

import Mathlib
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_adjWords
import Definitions.Def_MatMulDS_Supplement_coinFrac

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 8.23, p.63** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let
`β ≤ 1/50` be an admissible saving, fix `0 < γ ≤ 1`, and set `ξ = γβ/20`. Using the bounds (3.3) of [Uzn26], there is a randomized
algorithm that, given a connected undirected unweighted graph `G = (V, E)` with `n ≥ 2` vertices and `m ≤ n^{2−γ}` edges, returns,
with high probability, a `(3/2, 7/2)`-approximation of `diam(G)`, a `(5/3, 4)`-approximation of `e_G(v)` for every `v ∈ V`, and a
vertex `z` such that `e_G(z)` is a `(3/2, 5/2)`-approximation of `rad(G)`, and runs in `O_γ(n^{2−ξ}) = O_γ(n^{2−0.0000133γ})` time
with high probability.

**Formalization Note.**
* Randomized word RAM over `𝔽₂` (`coinFrac`), all steps counted, word size `w ≥ K⌈log₂(n+1)⌉ + K`; input `adjWords L`. Output:
  word cell `0` holds the estimate of `diam(G)`, cell `1 + v` that of `e_G(v)`, cell `n + 1` the vertex `z`. The estimates are
  integers: for an integer `x`, any real `x̃` with `x ≤ x̃ ≤ ρx + σ` can be rounded down to one.
* "With high probability" for both the outputs and the time: for every `c > 0` some `C` (depending on `c`, `γ`) such that with
  probability at least `1 − n^{−c}` the run halts within `C n^{2−ξ}` steps with correct outputs (the union of the two events).
* The program and constants depend on `γ` (`O_γ`). The numerical form `ξ ≥ 0.0000133 γ` at `β = 0.0002666` is the last conjunct. -/
theorem theorem_8_23 (β : ℝ) (hβ : AdmissibleSaving β) (hβ50 : β ≤ 1 / 50) (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) :
    (∃ (P : List AInstr) (K : ℕ),
      ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G L → G.Connected →
        (G.edgeSet.ncard : ℝ) ≤ (n : ℝ) ^ (2 - γ) →
        ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
          1 - (n : ℝ) ^ (-c) ≤ coinFrac P w (adjWords L) ⌈C * (n : ℝ) ^ (2 - γ * β / 20)⌉₊ fun st =>
            IsApprox (3 / 2) (7 / 2) (gdiam G) ((st 0).toInt : ℝ) ∧
            (∀ v : Fin n, IsApprox (5 / 3) 4 (ecc G v) ((st (1 + (v : ℕ))).toInt : ℝ)) ∧
            ∃ z : Fin n, (st ((n : ℤ) + 1)).toInt = ((z : ℕ) : ℤ) ∧
              IsApprox (3 / 2) (5 / 2) (grad G) (ecc G z : ℝ)) ∧
    0.0000133 * γ ≤ γ * 0.0002666 / 20 := by sorry

end MatMulDS.Supplement
