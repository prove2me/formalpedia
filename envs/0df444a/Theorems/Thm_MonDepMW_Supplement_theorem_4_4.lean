-- Prove2me | Theorems.Thm_MonDepMW_Supplement_theorem_4_4
-- name    : MonDepMW.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:32:56.722227+00:00
-- url     : https://prove2.me/theorems/4dc0229a-c172-45c8-9524-1ed1ad00d74f
-- title:
--   Theorem 4.4 — sequences of length $O(r/\varepsilon)$ whose radius-$r$ flip balls meet $O_{\mathcal C,r,\varepsilon}(n^\varepsilon)$ one-types, computable in $\hat O_{\mathcal C,r}(n^3)$ time
-- statement:
--   Let $r\ge1$ and let $\mathcal C$ be a monadically dependent graph class. Then for any rational $\varepsilon>0$ and any $n$-vertex graph $G\in\mathcal C$ there is a sequence of vertex subsets
--
--   $$\emptyset=B_m\subseteq B_{m-1}\subseteq\dots\subseteq B_1\subseteq B_0=V(G)$$
--
--   with $m\le O(r/\varepsilon)$ such that, for every $i\in[m]$ and $u\in V(G)$,
--
--   $$\mathrm{Ball}^r_{\mathcal T_1(G,B_i)}[u]\ \text{ intersects at most }\ O_{\mathcal C,r,\varepsilon}(n^\varepsilon)\ \text{ parts of }\ \mathcal T_1(G,B_{i-1}).$$
--
--   Here $\mathcal T_1(G,B)$ is the partition of $V(G)$ into 1-types over $B$, and $\mathrm{Ball}^r_{\mathcal P}[u]$ is the radius-$r$ ball around $u$ in the $\mathcal P$-flip metric (the intersection of the radius-$r$ balls of $u$ in all $\mathcal P$-flips of $G$). Moreover, there is one algorithm, independent of $\mathcal C$ and $r$, which given $\varepsilon$, $r$ and $G$ computes such a sequence and runs in time $\hat O_{\mathcal C,r}(n^3)$ for graphs $G\in\mathcal C$.
--
--   Precisely: there are an absolute constant $c_0$ and one program such that for all $r\ge1$ and monadically dependent $\mathcal C$ there is a subpolynomial $g$ such that for every rational $\varepsilon>0$ there is a constant $c$ for which every $n$-vertex $G\in\mathcal C$ has such a sequence with $m\le c_0(1+r/\varepsilon)$ and every ball meeting at most $c\cdot n^\varepsilon$ parts, and the program, on input $G$, $\varepsilon=p/q$ and $r$, outputs such a sequence (with the same $c_0$, $c$) within $(n+1)^3 g(n)$ steps.
--
--   This is the granularity-$n^\varepsilon$ variant of Theorem 4.3 used by the companion paper on first-order model checking.
--
--   **Formalization Note** The machine is the published word RAM; the program must work at every word size $W\ge b(\lfloor\log_2(n+p+q+r+2)\rfloor+1)$, with input $n$, the adjacency matrix, $p$, $q$, $r$, and its output is read by the mission's set-sequence decoder.
--
--   Differences from the source:
--
--   - reading: m ⩽ O(r/ε) → m ≤ c₀·(1 + r/ε) with c₀ an absolute constant; reason: B₀ = V(G) ≠ ∅ = B_m forces m ≥ 1 when n ≥ 1, so a literal bound c₀·r/ε fails for ε > c₀·r; the two agree for ε ≤ r, and the proof gives m ≤ 1 + 2r/ε
--   - encoding: O_{C,r,ε}(n^ε) → c·n^ε for every n, with a real c chosen after C, r, ε; reason: a ball meets at most n parts, so finitely many small n are absorbed into c
--   - encoding: Ô_{C,r}(n³) time → at most (n+1)³·g(n) steps, g subpolynomial, chosen after C and r and before ε; reason: the Ô convention of p.11 (hides subpolynomial factors), uniform in ε as printed; (n+1) instead of n only matters at n = 0
--   - encoding: an algorithm independent of C and r, given ε, r and G → one program P and word-size factor b chosen before r and C, on the published TrulySubcubicAPSP word RAM, input graphInput G ++ [p, q, r] for every representation ε = p/q with p, q ≥ 1, correct at every word size W ≥ b·(⌊log₂(n+p+q+r+2)⌋+1), output read by decodeSetSeq; reason: the RAM with words of length O(log n) (p.43) and the mission's fixed input/output layout
--   - encoding: r ∈ N → 1 ≤ r; reason: N is the positive integers (p.11)
--   - encoding: a graph class → MonDepMW.GraphClass (members on each Fin n); reason: every finite graph has a copy on some Fin n and all quantities are isomorphism invariant
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b06082b6e92c2408f95cd60971cd454258095371878ae2f448416bdfeb60b), Theorem 4.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_Subpolynomial
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_oneType
import Definitions.Def_MonDepMW_partsHit
import Definitions.Def_MonDepMW_IsFlip

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW.Supplement

/-- **Theorem 4.4.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded
Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §4, p.17 (PDF p.19): "Let r ∈ N and C be a monadically
dependent graph class. Then for any rational ε > 0 and any n-vertex graph G ∈ C, there is a sequence of vertex subsets
∅ = Bm ⊆ Bm−1 ⊆ . . . ⊆ B1 ⊆ B0 = V (G) with m ⩽ O(r/ε), which satisfies the following condition: For every i ∈ [m] and
u ∈ V (G), Ball^r_{𝒯1(G,Bi)}[u] intersects at most O_{C,r,ε}(n^ε) parts of 𝒯1(G, Bi−1). Moreover, there is an algorithm
(independent of C and r) which, given ε, r, and G, computes such a sequence B0, B1, . . . , Bm, and runs in time
Ô_{C,r}(n³) for graphs G ∈ C."

**Formalization Note.** Quantifier order: the absolute constant `c₀` of `O(r/ε)`, the program `P` and its word-size
factor `b` come first ("independent of C and r"); then `r ≥ 1` and `𝒞`; then the subpolynomial `g` of `Ô_{C,r}(n³)`
(independent of `ε`); then `ε`; then the constant `c` of `O_{C,r,ε}(n^ε)`, shared by both clauses. `m ⩽ O(r/ε)` is
`m ≤ c₀ · (1 + r/ε)`: since `B₀ = V(G) ≠ ∅ = B_m` forces `m ≥ 1` when `n ≥ 1`, a bound `c₀ · r/ε` with `c₀` absolute
fails for `ε > c₀ r`; the proof gives `m ≤ 1 + 2r/ε`. `O_{C,r,ε}(n^ε)` is `c · n^ε` for all `n` (finitely many small
`n` are absorbed into `c`, as at most `n` parts exist). `Ô_{C,r}(n³)` is `(n + 1)³ · g(n)` with `g` subpolynomial.
The ball `Ball^r_{𝒯₁(G,B_i)}[u]` is the published flip-metric ball `flipBall G (oneType G (B i)) r u`.
Input of the algorithm: `graphInput G` (`n`, then the adjacency matrix), then `p`, `q`, `r`, where `ε = p/q` with
`p, q ≥ 1` (any representation of `ε`); it must work at every word size `W ≥ b · (⌊log₂(n + p + q + r + 2)⌋ + 1)`.
Output: read by `decodeSetSeq` (`m`, then `m + 1` blocks of `n` bits, block `i` being `B_i`). -/
theorem theorem_4_4 :
    ∃ (c₀ : ℕ) (P : List Instr) (b : ℕ), ∀ (r : ℕ), 1 ≤ r → ∀ 𝒞 : GraphClass, MonadicallyDependent 𝒞 →
      ∃ g : ℕ → ℕ, Subpolynomial g ∧ ∀ ε : ℚ, 0 < ε → ∃ c : ℝ,
        (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
          ∃ (m : ℕ) (B : ℕ → Finset (Fin n)),
            (m : ℝ) ≤ (c₀ : ℝ) * (1 + (r : ℝ) / (ε : ℝ)) ∧ B 0 = Finset.univ ∧ B m = ∅ ∧
            (∀ i, i < m → B (i + 1) ⊆ B i) ∧
            ∀ i, 1 ≤ i → i ≤ m → ∀ u : Fin n,
              (partsHit (oneType G (B (i - 1))) (flipBall G (oneType G (B i)) r u) : ℝ) ≤
                c * (n : ℝ) ^ (ε : ℝ)) ∧
        ∀ (p q : ℕ), 1 ≤ p → 1 ≤ q → ((p : ℚ) / (q : ℚ) = ε) →
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ W : ℕ,
            b * (Nat.log2 (n + p + q + r + 2) + 1) ≤ W →
            RunsWithin P W ((n + 1) ^ 3 * g n) (graphInput G ++ [(p : ℤ), (q : ℤ), (r : ℤ)]) fun out =>
              ((decodeSetSeq n out).1 : ℝ) ≤ (c₀ : ℝ) * (1 + (r : ℝ) / (ε : ℝ)) ∧
              (decodeSetSeq n out).2 0 = Finset.univ ∧
              (decodeSetSeq n out).2 (decodeSetSeq n out).1 = ∅ ∧
              (∀ i, i < (decodeSetSeq n out).1 →
                (decodeSetSeq n out).2 (i + 1) ⊆ (decodeSetSeq n out).2 i) ∧
              ∀ i, 1 ≤ i → i ≤ (decodeSetSeq n out).1 → ∀ u : Fin n,
                (partsHit (oneType G ((decodeSetSeq n out).2 (i - 1)))
                    (flipBall G (oneType G ((decodeSetSeq n out).2 i)) r u) : ℝ) ≤
                  c * (n : ℝ) ^ (ε : ℝ) := by sorry

end MonDepMW.Supplement
