-- Prove2me | Theorems.Thm_GrossmanInevitable_Intersection_corollary_1_7
-- name    : GrossmanInevitable.Intersection.corollary_1_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:06:46.725787+00:00
-- url     : https://prove2.me/theorems/8755a093-1df3-44ec-9678-6f4c4169df8f
-- title:
--   Corollary 1.7 — finding an element of a ∩ b is O(√n log n)-R-inevitable for computing ⟨a, b⟩
-- statement:
--   Let $a,b\in\{0,1\}^n$ be Alice's and Bob's inputs. Finding an element of $a\cap b$ is $O(\sqrt n\log n)$-R-inevitable for computing $\langle a,b\rangle$. That is, there is a constant $C$ such that the following holds for every $n\ge 1$ and every deterministic protocol $\pi$ that computes $\langle a,b\rangle$ (over the integers). There is a zero-error protocol using private randomness that, given $\pi(a,b)$ as shared advice, outputs an element of $a\cap b$ if $a\cap b\ne\emptyset$ and $\bot$ otherwise, with probability $1$. Its expected communication is at most
--   $$C\cdot\sqrt n\cdot\log_2 n$$
--   on every input pair. The constant $C$ is chosen before $n$ and $\pi$.
--
--   Differences from the source:
--   - encoding: O(g)-inevitable, the O(·) constant independent of n and s (footnote 15, proof of Corollary 1.7) → ∃ C : ℝ, stated before n, s and the protocol; α = ENNReal.ofReal (C · g); reason: uniform constant as the proofs state; a negative C only makes the bound 0
--   - encoding: α with values in ℕ ∪ {∞} → α with values in [0, ∞] (ENNReal), here ofReal of the real bound; reason: a bit count in ℕ is ≤ x iff it is ≤ ⌊x⌋; for expected cost, ⌊C·g⌋ and C·g are within a factor 2 once C·g ≥ 1, and g is 0 or ≥ 1 on the stated range, so the O(·) classes coincide
--   - encoding: log, log²(1 + n/s) → Real.logb 2, (Real.logb 2 (1 + n/s))^2; reason: logarithms are base two (§2); log² x means (log x)²
--   - encoding: a, b ∈ {0, 1}^n, witnesses in [n] = {1, …, n} → Fin n → Bool (true = 1), witnesses in Fin n, indexed from 0; reason: Lean convention; a relabelling of indices
--   - encoding: outputs in W ∪ {⊥} → Option W (none = ⊥); correctness CorrectOut: some w with R a b w, or none when (a, b) has no witness; reason: Lean convention; same instances
--   - encoding: πR(a, b, σ), a protocol run with the advice string σ ∈ {0,1}* known to both players → a family of protocols indexed by σ : List Bool, run on σ = transcript πf a b; reason: the next speaker, the bit functions and the output may all depend on σ; same instances
--   - encoding: a zero-error protocol using private randomness (Las Vegas protocol): private random sources, with probability 1 terminates with a correct output determined by the transcript; cost = expected communication → LVProtocol: next speaker/output a function of (advice, bits so far); Alice's bit a measurable function of (advice, bits so far, a, ωA), Bob's of (advice, bits so far, b, ωB); ωA, ωB independent i.i.d. fair-coin sequences (coins.prod coins); ZeroErrorOn = a.s. stops with CorrectOut output; expCost = ∫⁻ of the number of bits in [0, ∞]; reason: private randomness modelled as each player's own infinite sequence of fair coins; runs are unbounded, so termination is only almost sure and non-termination costs ∞
--   - encoding: a deterministic protocol in which the players alternately send messages whose lengths are determined by the past messages; its transcript π(a, b) and output val(π(a, b)) → the published binary protocol tree OneOfManyCC.Protocol; transcript = the list of bits along the path to the leaf, val = Protocol.eval (the leaf label); reason: the standard equivalent tree form of a deterministic protocol (each bit sent is an inner node of its sender); same transcripts, outputs and costs
--   - encoding: a, b ∈ {0,1}^n with n unrestricted → 1 ≤ n; reason: nondegeneracy: at n = 0 the bound √n log n involves log 0, which is undefined
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), Corollary 1.7, p. 5 (PDF 7); restated with proof in §3.2.2, p. 23 (PDF 25)

import Mathlib
import Definitions.Def_GrossmanInevitable_Intersection_Inevitable
import Definitions.Def_GrossmanInevitable_Intersection_DotProduct

namespace GrossmanInevitable.Intersection

/-- **Corollary 1.7** (printed p. 5 / PDF 7; restated with proof, printed p. 23 / PDF 25). Finding
an element of `a ∩ b` is `O(√n log n)`-R-inevitable for computing `⟨a, b⟩`: there is one constant
`C`, chosen before `n` and the protocol, such that for every `n ≥ 1` and every deterministic
protocol `π` computing `⟨a, b⟩` (over the integers) there is a zero-error protocol using private
randomness that, given the transcript `π(a, b)` as shared advice, outputs an element of `a ∩ b` if
`a ∩ b ≠ ∅` and `⊥` otherwise, with expected communication at most `C · √n · log₂ n` on every
input pair (Definition 3.1 with the constant `α`, finite on every input). -/
theorem corollary_1_7 :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      IsRInevitable (fun a b : Fin n → Bool => dot a b) (IntersectionRel n)
        (fun _ _ => ENNReal.ofReal (C * Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ))) := by sorry

end GrossmanInevitable.Intersection
