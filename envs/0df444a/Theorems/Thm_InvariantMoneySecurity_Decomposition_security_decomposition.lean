-- Prove2me | Theorems.Thm_InvariantMoneySecurity_Decomposition_security_decomposition
-- name    : InvariantMoneySecurity.Decomposition.security_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:02:37.831079+00:00
-- url     : https://prove2.me/theorems/e1ef3833-9e5d-4097-90f7-de067dcefdd1
-- title:
--   Theorem 6.7 — security decomposition
-- statement:
--   Let $D$ be an invariant quantum money scheme, with its actual mint, finite-round lazy verifier, and uniform quantum polynomial-time adversaries. Security means negligible probability of producing two registers accepted at the issued serial number. Preparation means negligible average accepted weight from classical measured-mint data. Transfer compares every coherent forger with some measure-first forger using one polynomial independent of the adversary. Then both conclusions hold:
--   $$\bigl(\neg\mathrm{Preparation}(D)\Rightarrow\neg\mathrm{Secure}(D)\bigr)\ \land\ \bigl(\mathrm{RapidMixing}(D)\Rightarrow[\neg\mathrm{Secure}(D)\iff(\neg\mathrm{Preparation}(D)\lor\neg\mathrm{Transfer}(D))]\bigr).$$
--   A preparation failure implies insecurity without rapid mixing. With rapid mixing, the two assumptions together characterize security. Outputs can be entangled, serials follow the nonuniform mint law, and every same-serial orbit contributes to accepted weight. No orbit-injectivity or path-finding assumption is imposed. This is the full two-part source target.
--
--   Differences from the source:
--   - encoding: logical object registers and public serials → padded qubit registers, polynomial-width public serial encoding, and a dummy n = 0 instance; reason: valid states embed isometrically; invalid encodings reject; reversible serial padding preserves equality and mint weights; finite initial values do not affect negligibility
--   - encoding: uniform QPT algorithms with arbitrary workspace, randomization, and measurement → recoverable uniform circuits with effectively approximable at-most-three-qubit unitary gates and final partial trace; reason: coherent records defer measurements and classical control; polynomial numerical precision gives negligible implementation error
--   - generalization: the uniform superposition over X prepared by a uniform family of polynomial-size circuits → prepared up to negligible infidelity by such a family, with discarded wires allowed; reason: exact preparation is the zero-error case, so every source scheme is included; negligible infidelity and negligible trace distance are equivalent for pure targets
--   - generalization: a polynomial verifier round count → any uniformly computable polynomially bounded positive round count; reason: the source proofs use only efficiency of the round count and the eventual product rΔ, so the source case is included without altering any bound
--   - generalization: a verifier used as an efficient public procedure, whose Algorithm 1 prepares the uniform move register → no clause in the scheme that Algorithm 1 is efficient; reason: Definition 2.1 lists no such component and neither this theorem nor its proof runs the verifier inside an algorithm, so every source scheme is included
--   - encoding: the game as two runs of Algorithm 1, win^M as win of A∘M, and move labels 1 to |S| → the joint Born probability of the tensor effect from equation (5), win^M as the average of equation (15) over the measured mint law, and zero-based binary labels at the bit width of |S|; reason: equation (5) is the source's formula for the accepting branch; by linearity measuring and then running equals the average in equation (15); shifting a label changes no move
--   - encoding: negligible means μ(n) < 1/q(n) for every polynomial q → the same bound for every real polynomial positive at all natural numbers; reason: a polynomial with zero or negative values at large n gives no meaningful bound, and every other polynomial is dominated by one positive at all natural numbers
--   - encoding: polynomial factors and negligible errors → a polynomial positive at all natural inputs and a nonnegative negligible error; reason: dominating a polynomial by a positive polynomial and taking the positive part of an error preserves the same transfer property since winning probabilities are nonnegative
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 28, Theorem 6.7, parts (i) and (ii); proof p. 29

import Definitions.Def_InvariantMoneySecurity_Decomposition_SecurityAssumptions
set_option autoImplicit false

namespace InvariantMoneySecurity.Decomposition

/-- Both parts of Theorem 6.7, p. 28. Part (i) has no rapid-mixing hypothesis. -/
theorem security_decomposition (D : Scheme) :
    (¬ D.Preparation → ¬ D.Secure) ∧
    (D.RapidMixing → (¬ D.Secure ↔ (¬ D.Preparation ∨ ¬ D.Transfer))) := by sorry

end InvariantMoneySecurity.Decomposition
