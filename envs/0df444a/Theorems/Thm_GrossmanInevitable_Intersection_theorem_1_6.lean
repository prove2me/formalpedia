-- Prove2me | Theorems.Thm_GrossmanInevitable_Intersection_theorem_1_6
-- name    : GrossmanInevitable.Intersection.theorem_1_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:06:41.802217+00:00
-- url     : https://prove2.me/theorems/9385d5b0-a84e-4af1-b7ba-62a9e2d6e1fa
-- title:
--   Theorem 1.6 — finding an element of a ∩ b is O(min{√n log n, s log²(1 + n/s)})-R-inevitable for deciding ⟨a, b⟩ = s
-- statement:
--   Let $a,b\in\{0,1\}^n$ be Alice's and Bob's inputs, and let $1\le s\le n$ be an integer. Finding an element of $a\cap b$ is $O(\min\{\sqrt n\log n,\ s\log^2(1+n/s)\})$-R-inevitable for deciding whether $\langle a,b\rangle=s$.
--
--   In Lean, there is one constant $C$, chosen before $n$ and $s$, such that for all integers $1\le s\le n$ the following holds. For every deterministic protocol $\pi_f$ deciding $\mathrm{DP}_s$ there is a zero-error protocol using private randomness $\pi_R$ with advice such that, on every input with $\langle a,b\rangle=s$ and given $\pi_f(a,b)$, it outputs an element of $a\cap b$ with probability $1$. Its expected communication is at most
--   $$C\cdot\min\{\sqrt n\cdot\log_2 n,\ s\cdot\log_2^2(1+n/s)\}.$$
--
--   Differences from the source:
--   - encoding: O(g)-inevitable, the O(·) constant independent of n and s (footnote 15, proof of Corollary 1.7) → ∃ C : ℝ, stated before n, s and the protocol; α = ENNReal.ofReal (C · g); reason: uniform constant as the proofs state; a negative C only makes the bound 0
--   - encoding: α with values in ℕ ∪ {∞} → α with values in [0, ∞] (ENNReal), here ofReal of the real bound; reason: a bit count in ℕ is ≤ x iff it is ≤ ⌊x⌋; for expected cost, ⌊C·g⌋ and C·g are within a factor 2 once C·g ≥ 1, and g is 0 or ≥ 1 on the stated range, so the O(·) classes coincide
--   - encoding: log, log²(1 + n/s) → Real.logb 2, (Real.logb 2 (1 + n/s))^2; reason: logarithms are base two (§2); log² x means (log x)²
--   - encoding: a, b ∈ {0, 1}^n, witnesses in [n] = {1, …, n} → Fin n → Bool (true = 1), witnesses in Fin n, indexed from 0; reason: Lean convention; a relabelling of indices
--   - encoding: Definition 1.2: f : A × B → {0, 1}, constant α, requirement on f⁻¹(1) → f : A → B → Bool; Definition 3.1 with α(a, b) = α on f⁻¹(1) and ∞ on f⁻¹(0); reason: the paper's own remark (printed p. 17) that Definition 1.2 is this special case of Definition 3.1
--   - encoding: outputs in W ∪ {⊥} → Option W (none = ⊥); correctness CorrectOut: some w with R a b w, or none when (a, b) has no witness; reason: Lean convention; same instances
--   - encoding: πR(a, b, σ), a protocol run with the advice string σ ∈ {0,1}* known to both players → a family of protocols indexed by σ : List Bool, run on σ = transcript πf a b; reason: the next speaker, the bit functions and the output may all depend on σ; same instances
--   - encoding: a zero-error protocol using private randomness (Las Vegas protocol): private random sources, with probability 1 terminates with a correct output determined by the transcript; cost = expected communication → LVProtocol: next speaker/output a function of (advice, bits so far); Alice's bit a measurable function of (advice, bits so far, a, ωA), Bob's of (advice, bits so far, b, ωB); ωA, ωB independent i.i.d. fair-coin sequences (coins.prod coins); ZeroErrorOn = a.s. stops with CorrectOut output; expCost = ∫⁻ of the number of bits in [0, ∞]; reason: private randomness modelled as each player's own infinite sequence of fair coins; runs are unbounded, so termination is only almost sure and non-termination costs ∞
--   - encoding: a deterministic protocol in which the players alternately send messages whose lengths are determined by the past messages; its transcript π(a, b) and output val(π(a, b)) → the published binary protocol tree OneOfManyCC.Protocol; transcript = the list of bits along the path to the leaf, val = Protocol.eval (the leaf label); reason: the standard equivalent tree form of a deterministic protocol (each bit sent is an inner node of its sender); same transcripts, outputs and costs
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), Theorem 1.6, p. 5 (PDF 7); restated with proof in §3.2.2, p. 23 (PDF 25)

import Mathlib
import Definitions.Def_GrossmanInevitable_Intersection_Inevitable
import Definitions.Def_GrossmanInevitable_Intersection_DotProduct

namespace GrossmanInevitable.Intersection

/-- **Theorem 1.6** (printed p. 5 / PDF 7; restated with proof, printed p. 23 / PDF 25). Finding
an element of `a ∩ b` is `O(min{√n log n, s log²(1 + n/s)})`-R-inevitable for deciding whether
`⟨a, b⟩ = s`: there is one constant `C`, chosen before `n` and `s`, such that for all integers
`1 ≤ s ≤ n` the relation `Intersection` (`IntersectionRel n`) is `C · min{√n · log₂ n, s · log₂²(1 + n/s)}`-R-inevitable
for `DP_s` (Definition 1.2: a zero-error private-randomness `πR`, expected bits on the inputs with
`⟨a, b⟩ = s`). -/
theorem theorem_1_6 :
    ∃ C : ℝ, ∀ n s : ℕ, 1 ≤ s → s ≤ n →
      IsRInevitableBool (dpEq n s) (IntersectionRel n)
        (ENNReal.ofReal (C * min (Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ))
          ((s : ℝ) * (Real.logb 2 (1 + (n : ℝ) / (s : ℝ))) ^ 2))) := by sorry

end GrossmanInevitable.Intersection
