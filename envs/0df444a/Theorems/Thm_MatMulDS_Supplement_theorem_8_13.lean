-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_8_13
-- name    : MatMulDS.Supplement.theorem_8_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:21:01.369299+00:00
-- url     : https://prove2.me/theorems/94c66eb2-de9d-4373-9997-405c47d95abd
-- title:
--   Theorem 8.13 — reachability from $S$ in $O((m+n|S|)^{4/3-\xi})$, $\xi=2\beta/(9+25\beta)$
-- statement:
--   Let $\beta\le1/50$ be an admissible saving, and set $\xi=2\beta/(9+25\beta)$. Using the bounds (3.3) of [Uzn26], there is a deterministic algorithm that, given a directed graph $G=(V,E)$ with $n$ vertices and $m$ edges and a nonempty set $S\subseteq V$, decides whether $v$ is reachable from $s$ for all $(s,v)\in S\times V$ in
--   $$O((m+n|S|)^{4/3-\xi})=O((m+n|S|)^{1.3332742})$$
--   time.
--
--   For $m\le n^{3/2}$ and $|S|\le\lceil\sqrt n\rceil$ this is $O(n^{2-3\xi/2})$, below the quadratic barrier of earlier algorithms.
--
--   Differences from the source:
--   - generalization: an algorithm on the word RAM with $\Theta(\log n)$-bit words → one word program of the mission's machine for every word size $w\ge K\lceil\log_2(n+1)\rceil+K$, all steps counted; reason: it specializes to each word size above the threshold and cannot exploit a huge word
--   - reading: "Using the bounds (3.3) of [Uzn26]" → no hypothesis; reason: it names a cited theorem the proof uses; assuming it would weaken the statement (SUPPLEMENT decision 2)
--   - encoding: a directed graph with $m$ edges; output → out-neighbour lists without repetitions, $m=\sum_v|L_v|$; word cell $kn+v$ is $1$ if $v$ is reachable from $S_k$ and $0$ otherwise; reason: the source's input convention and a layout
--   - encoding: $O(\cdot)$ → $C\cdot$ with $C$ fixed before the sizes, inside a ceiling as a step budget; reason: the meaning of $O$ for one fixed algorithm
--   - encoding: the numerical form $O((m+n|S|)^{1.3332742})$ → a separate conjunct, the inequality at $\beta=0.0002666$; reason: the source evaluates its bound at the admissible saving of Theorem 7.4
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 8.13, p.58 (PDF p.60)

import Mathlib
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_adjWords

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 8.13, p.58** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let
`β ≤ 1/50` be an admissible saving, and set `ξ = 2β/(9 + 25β)`. Using the bounds (3.3) of [Uzn26], there is a deterministic
algorithm that, given a directed graph `G = (V, E)` with `n` vertices and `m` edges and a nonempty set `S ⊆ V`, decides whether `v`
is reachable from `s` for all `(s, v) ∈ S × V` in `O((m + n|S|)^{4/3−ξ}) = O((m + n|S|)^{1.3332742})` time.

**Formalization Note.**
* The graph is given by out-neighbour lists `L` (each without repetitions), `m = Σ_v |L v|`, and `S` by a list without repetitions;
  input words `adjWords L ++ vtxWords S`. Output: word cell `k n + v` is `1` if `v` is reachable from the `k`-th source and `0`
  otherwise. A word program of the published machine, all steps counted, word size `w ≥ K⌈log₂(n+1)⌉ + K`.
* "Using the bounds (3.3) of [Uzn26]" names a cited theorem the proof uses; it is not a hypothesis.
* The numerical form is the instance `β = 0.0002666`, stated as the last conjunct. -/
theorem theorem_8_13 (β : ℝ) (hβ : AdmissibleSaving β) (hβ50 : β ≤ 1 / 50) :
    (∃ (P : List AInstr) (K : ℕ) (C : ℝ), 0 < C ∧ IsWordProgram P ∧
      ∀ (n : ℕ) (L : Fin n → List (Fin n)) (S : List (Fin n)), (∀ v, (L v).Nodup) → S.Nodup → S ≠ [] →
      ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
        ∃ st : ℤ → BitVec w,
          wordRun P w (adjWords L ++ vtxWords S)
            ⌈C * (((∑ v, (L v).length : ℕ) : ℝ) + (n : ℝ) * S.length) ^ ((4 : ℝ) / 3 - 2 * β / (9 + 25 * β))⌉₊ =
              some st ∧
          ∀ (k : Fin S.length) (v : Fin n),
            ((st ((k : ℤ) * n + (v : ℕ))).toInt = 1 ∧ DiReach L S[k] v) ∨
            ((st ((k : ℤ) * n + (v : ℕ))).toInt = 0 ∧ ¬ DiReach L S[k] v)) ∧
    (4 : ℝ) / 3 - 2 * 0.0002666 / (9 + 25 * 0.0002666) ≤ 1.3332742 := by sorry

end MatMulDS.Supplement
