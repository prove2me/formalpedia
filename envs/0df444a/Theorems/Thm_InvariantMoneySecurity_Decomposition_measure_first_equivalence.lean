-- Prove2me | Theorems.Thm_InvariantMoneySecurity_Decomposition_measure_first_equivalence
-- name    : InvariantMoneySecurity.Decomposition.measure_first_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:02:07.853473+00:00
-- url     : https://prove2.me/theorems/aa86a610-05b1-4f6f-be63-ed601226aff4
-- title:
--   Theorem 6.5 — measure-first security and the preparation assumption
-- statement:
--   Let $D$ be an invariant money scheme. Write $\mathrm{Preparation}(D)$ for negligible average accepted weight for every QPT preparer with classical measured-mint input, and let $\mathrm{MF}(D)$ mean that some uniform QPT forger has non-negligible measure-first winning probability. Then
--   $$\bigl(\neg\mathrm{Preparation}(D)\Rightarrow\mathrm{MF}(D)\bigr)\ \land\ \bigl(\mathrm{RapidMixing}(D)\Rightarrow[\mathrm{MF}(D)\iff\neg\mathrm{Preparation}(D)]\bigr).$$
--   The first implication has no rapid-mixing premise. The equivalence asserts existence of an adversary, rather than a statement about each fixed adversary. The forger may perform arbitrary quantum computation after the initial measurement. This theorem supplies both the unconditional attack direction and the rapidly mixing equivalence needed by the security decomposition.
--
--   Differences from the source:
--   - encoding: logical object registers and public serials → padded qubit registers, polynomial-width public serial encoding, and a dummy n = 0 instance; reason: valid states embed isometrically; invalid encodings reject; reversible serial padding preserves equality and mint weights; finite initial values do not affect negligibility
--   - encoding: uniform QPT algorithms with arbitrary workspace, randomization, and measurement → recoverable uniform circuits with effectively approximable at-most-three-qubit unitary gates and final partial trace; reason: coherent records defer measurements and classical control; polynomial numerical precision gives negligible implementation error
--   - generalization: the uniform superposition over X prepared by a uniform family of polynomial-size circuits → prepared up to negligible infidelity by such a family, with discarded wires allowed; reason: exact preparation is the zero-error case, so every source scheme is included; negligible infidelity and negligible trace distance are equivalent for pure targets
--   - generalization: a polynomial verifier round count → any uniformly computable polynomially bounded positive round count; reason: the source proofs use only efficiency of the round count and the eventual product rΔ, so the source case is included without altering any bound
--   - generalization: a verifier used as an efficient public procedure, whose Algorithm 1 prepares the uniform move register → no clause in the scheme that Algorithm 1 is efficient; reason: Definition 2.1 lists no such component and neither this theorem nor its proof runs the verifier inside an algorithm, so every source scheme is included
--   - encoding: the game as two runs of Algorithm 1, win^M as win of A∘M, and move labels 1 to |S| → the joint Born probability of the tensor effect from equation (5), win^M as the average of equation (15) over the measured mint law, and zero-based binary labels at the bit width of |S|; reason: equation (5) is the source's formula for the accepting branch; by linearity measuring and then running equals the average in equation (15); shifting a label changes no move
--   - encoding: negligible means μ(n) < 1/q(n) for every polynomial q → the same bound for every real polynomial positive at all natural numbers; reason: a polynomial with zero or negative values at large n gives no meaningful bound, and every other polynomial is dominated by one positive at all natural numbers
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 28, Theorem 6.5

import Definitions.Def_InvariantMoneySecurity_Decomposition_SecurityAssumptions
set_option autoImplicit false

namespace InvariantMoneySecurity.Decomposition

/-- Theorem 6.5, p. 28, including its final unconditional implication. -/
theorem measure_first_equivalence (D : Scheme) :
    (¬ D.Preparation → D.MeasureFirstFailure) ∧
    (D.RapidMixing → (D.MeasureFirstFailure ↔ ¬ D.Preparation)) := by sorry

end InvariantMoneySecurity.Decomposition
