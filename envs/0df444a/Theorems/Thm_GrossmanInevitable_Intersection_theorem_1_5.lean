-- Prove2me | Theorems.Thm_GrossmanInevitable_Intersection_theorem_1_5
-- name    : GrossmanInevitable.Intersection.theorem_1_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:06:36.298528+00:00
-- url     : https://prove2.me/theorems/7d9687d3-5991-4857-b25a-2f6e05b63ff3
-- title:
--   Theorem 1.5 — computing a ∩ b is O(s log²(1 + n/s))-inevitable for deciding ⟨a, b⟩ ≤ s
-- statement:
--   Let $a,b\in\{0,1\}^n$ be Alice's and Bob's inputs, and let $1\le s\le n$ be an integer. Computing $a\cap b$ is $O(s\log^2(1+n/s))$-inevitable for deciding whether $\langle a,b\rangle\le s$.
--
--   In Lean, there is one constant $C$, chosen before $n$ and $s$, such that for all integers $1\le s\le n$ the following holds. For every deterministic protocol $\pi_f$ deciding $\mathrm{DP}_{\le s}$ there is a deterministic protocol $\pi_R$ with advice such that, on every input with $\langle a,b\rangle\le s$ and given $\pi_f(a,b)$, it outputs the set $a\cap b$ using at most
--   $$C\cdot s\cdot\log_2^2(1+n/s)$$
--   bits. This is Definition 1.2 for the relation $R_g$ of $g(a,b)=a\cap b$ (Definition 3.2).
--
--   Differences from the source:
--   - encoding: O(g)-inevitable, the O(·) constant independent of n and s (footnote 15, proof of Corollary 1.7) → ∃ C : ℝ, stated before n, s and the protocol; α = ENNReal.ofReal (C · g); reason: uniform constant as the proofs state; a negative C only makes the bound 0
--   - encoding: α with values in ℕ ∪ {∞} → α with values in [0, ∞] (ENNReal), here ofReal of the real bound; reason: a bit count in ℕ is ≤ x iff it is ≤ ⌊x⌋; for expected cost, ⌊C·g⌋ and C·g are within a factor 2 once C·g ≥ 1, and g is 0 or ≥ 1 on the stated range, so the O(·) classes coincide
--   - encoding: log, log²(1 + n/s) → Real.logb 2, (Real.logb 2 (1 + n/s))^2; reason: logarithms are base two (§2); log² x means (log x)²
--   - encoding: a, b ∈ {0, 1}^n, witnesses in [n] = {1, …, n} → Fin n → Bool (true = 1), witnesses in Fin n, indexed from 0; reason: Lean convention; a relabelling of indices
--   - encoding: Definition 1.2: f : A × B → {0, 1}, constant α, requirement on f⁻¹(1) → f : A → B → Bool; Definition 3.1 with α(a, b) = α on f⁻¹(1) and ∞ on f⁻¹(0); reason: the paper's own remark (printed p. 17) that Definition 1.2 is this special case of Definition 3.1
--   - encoding: outputs in W ∪ {⊥} → Option W (none = ⊥); correctness CorrectOut: some w with R a b w, or none when (a, b) has no witness; reason: Lean convention; same instances
--   - encoding: πR(a, b, σ), a protocol run with the advice string σ ∈ {0,1}* known to both players → a family of protocols indexed by σ : List Bool, run on σ = transcript πf a b; reason: the next speaker, the bit functions and the output may all depend on σ; same instances
--   - encoding: a deterministic protocol in which the players alternately send messages whose lengths are determined by the past messages; its transcript π(a, b) and output val(π(a, b)) → the published binary protocol tree OneOfManyCC.Protocol; transcript = the list of bits along the path to the leaf, val = Protocol.eval (the leaf label); reason: the standard equivalent tree form of a deterministic protocol (each bit sent is an inner node of its sender); same transcripts, outputs and costs
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), Theorem 1.5, p. 5 (PDF 7); restated with proof in §3.2.1, pp. 21–22 (PDF 23–24), constant 16 in footnote 15

import Mathlib
import Definitions.Def_GrossmanInevitable_Intersection_Inevitable
import Definitions.Def_GrossmanInevitable_Intersection_DotProduct

namespace GrossmanInevitable.Intersection

/-- **Theorem 1.5** (printed p. 5 / PDF 7; restated with proof, printed pp. 21–22 / PDF 23–24).
Computing `a ∩ b` is `O(s log²(1 + n/s))`-inevitable for deciding whether `⟨a, b⟩ ≤ s`: there is
one constant `C`, chosen before `n` and `s`, such that for all integers `1 ≤ s ≤ n` the relation
`R_g` of `g(a, b) = a ∩ b` (Definition 3.2) is `C · s · log₂²(1 + n/s)`-inevitable for `DP_{≤s}`
(Definition 1.2: deterministic `πR`, worst-case bits on the inputs with `⟨a, b⟩ ≤ s`). -/
theorem theorem_1_5 :
    ∃ C : ℝ, ∀ n s : ℕ, 1 ≤ s → s ≤ n →
      IsInevitableBool (dpLe n s) (graphRel (fun a b : Fin n → Bool => inter a b))
        (ENNReal.ofReal (C * (s : ℝ) * (Real.logb 2 (1 + (n : ℝ) / (s : ℝ))) ^ 2)) := by sorry

end GrossmanInevitable.Intersection
