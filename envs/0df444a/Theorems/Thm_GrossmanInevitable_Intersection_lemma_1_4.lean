-- Prove2me | Theorems.Thm_GrossmanInevitable_Intersection_lemma_1_4
-- name    : GrossmanInevitable.Intersection.lemma_1_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:06:42.799269+00:00
-- url     : https://prove2.me/theorems/596944a4-7c8c-4ed3-8226-97c301254a6c
-- title:
--   Lemma 1.4 — rectangle characterization of inevitability
-- statement:
--   Let $A$ and $B$ be finite input domains, let $R\subseteq A\times B\times W$ be a relation, and let $f:A\times B\to\{0,1\}$ be a decision problem such that every input in $f^{-1}(1)$ has an $R$-witness. For a rectangle $X\times Y$, let $D(R\mid X\times Y)$ be the minimum worst-case communication of a deterministic protocol that finds an $R$-witness on every input pair in $X\times Y$. Then the least $\alpha\in\mathbb N$ for which $R$ is $\alpha$-inevitable for $f$ (Definition 1.2) is
--   $$\max_{\emptyset\ne X\times Y\subseteq f^{-1}(1)} D(R\mid X\times Y),$$
--   where the maximum over an empty set is $0$. In Lean: `IsLeast {α : ℕ | IsInevitableBool f R α} (oneRectMax f R)`.
--
--   Differences from the source:
--   - encoding: Definition 1.2: f : A × B → {0, 1}, constant α, requirement on f⁻¹(1) → f : A → B → Bool; Definition 3.1 with α(a, b) = α on f⁻¹(1) and ∞ on f⁻¹(0); reason: the paper's own remark (printed p. 17) that Definition 1.2 is this special case of Definition 3.1
--   - encoding: outputs in W ∪ {⊥} → Option W (none = ⊥); correctness CorrectOut: some w with R a b w, or none when (a, b) has no witness; reason: Lean convention; same instances
--   - encoding: πR(a, b, σ), a protocol run with the advice string σ ∈ {0,1}* known to both players → a family of protocols indexed by σ : List Bool, run on σ = transcript πf a b; reason: the next speaker, the bit functions and the output may all depend on σ; same instances
--   - encoding: a deterministic protocol in which the players alternately send messages whose lengths are determined by the past messages; its transcript π(a, b) and output val(π(a, b)) → the published binary protocol tree OneOfManyCC.Protocol; transcript = the list of bits along the path to the leaf, val = Protocol.eval (the leaf label); reason: the standard equivalent tree form of a deterministic protocol (each bit sent is an inner node of its sender); same transcripts, outputs and costs
--   - encoding: D(R|X×Y): protocols that find an R-witness on every pair of X × Y → DPromise R (X ×ˢ Y): protocols with Option W output, correct (CorrectOut) on every pair of X × Y; reason: on a rectangle inside f⁻¹(1) every pair has a witness, so a correct output is exactly a witness
--   - encoding: the least α; a maximum, 0 over an empty set → IsLeast over ℕ; sSup in ℕ of the finite set of values (sSup ∅ = 0); reason: for finite A, B the set of values is finite, so sSup is its maximum
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), Lemma 1.4, p. 4 (PDF 6); restated with proof in §3.1.1, p. 18 (PDF 20)

import Mathlib
import Definitions.Def_GrossmanInevitable_Intersection_Relation
import Definitions.Def_GrossmanInevitable_Intersection_Inevitable

namespace GrossmanInevitable.Intersection

/-- **Lemma 1.4** (printed p. 4 / PDF 6; restated with proof, printed p. 18 / PDF 20). Let `A`, `B`
be finite, `R ⊆ A × B × W` a relation and `f : A × B → {0, 1}` a decision problem such that every
input in `f⁻¹(1)` has an `R`-witness. Then the least `α ∈ ℕ` for which `R` is `α`-inevitable for
`f` (Definition 1.2) is `max_{∅ ≠ X × Y ⊆ f⁻¹(1)} D(R|X×Y)`, the maximum over an empty set being
`0` (`oneRectMax`). -/
theorem lemma_1_4 {A B W : Type} [Fintype A] [Fintype B] (R : A → B → W → Prop)
    (f : A → B → Bool) (hf : ∀ a b, f a b = true → ∃ w, R a b w) :
    IsLeast {α : ℕ | IsInevitableBool f R (α : ENNReal)} (oneRectMax f R) := by sorry

end GrossmanInevitable.Intersection
