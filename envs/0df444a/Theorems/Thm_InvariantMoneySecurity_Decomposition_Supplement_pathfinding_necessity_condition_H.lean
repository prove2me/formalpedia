-- Prove2me | Theorems.Thm_InvariantMoneySecurity_Decomposition_Supplement_pathfinding_necessity_condition_H
-- name    : InvariantMoneySecurity.Decomposition.Supplement.pathfinding_necessity_condition_H
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:34:24.464781+00:00
-- url     : https://prove2.me/theorems/fd3cff4e-2464-4c52-83ca-407a355940fd
-- title:
--   Theorem 4.8 — necessity of path-finding hardness under condition (H)
-- statement:
--   Let $(X,S,I)$ be an invariant money scheme and $G=(G_n)$ a family of seeds that satisfies condition (H), with coset parameterizations $(W_x,\varphi_x)$ acting through the moves. Let $A$ be a quantum polynomial-time path-finder and $q$ a real polynomial with $q(n)>0$ for every $n\in\mathbb N$.
--
--   1. If for every $n$ and every $x\in G_n$
--   $$\Pr_{y}\big[A(x,y)\text{ outputs a path from }x\text{ to }y\big]\ \ge\ \frac1{q(n)},$$
--   with $y$ uniform on $C_{k(x)}$, then orbit state preparation is solvable on $G$.
--   2. If for infinitely many $n$
--   $$\Pr\big[x\in G_n\text{ and }A(x,y)\text{ outputs a path from }x\text{ to }y\big]\ \ge\ \frac1{q(n)},$$
--   where $(p,x)\leftarrow M_n$ and $y$ is uniform on $C_{k(x)}$, then some quantum polynomial-time forger $B$ wins the unforgeability game of Definition 2.4 with probability at least $1/(3q(n))$ for infinitely many $n$, and so the scheme is not secure.
--
--   All probabilities include $A$'s internal measurements and randomness. No rapid mixing, no injectivity of $I$ on orbits and no other design condition is assumed. Under condition (H), the theorem says that security requires path-finding to be hard on a random target.
--
--   **Formalization Note** "Infinitely many $n$" is $\forall N\,\exists n\ge N$. The forger is a published uniform QPT forger and its winning probability is the published one, with the actual finite-round verifier. Both conclusions of part 2, the explicit bound and insecurity, are stated.
--
--   Differences from the source:
--   - encoding: "A outputs a path" → the measured output string decodes (unary length, then binary move indices in the scheme's index encoding; trailing bits ignored) to a word that is a path; reason: the source fixes no output encoding, and any polynomial-time encoding is transcoded by the path-finder itself.
--   - encoding: labels are bit strings of polynomial length → bit strings of one length $\ell(n)\le\mathrm{poly}(n)$; reason: padding with a length prefix is polynomial-time and changes no group.
--   - encoding: the group operations, the action and $g_s$ "computable in polynomial time from $x$" → polynomial-time classical functions on codes of $(1^n,x,\text{operands})$ that are correct on valid operands, with the group and action laws as hypotheses on the data at every seed; the identity $1_W$ is not required to be computable; reason: the source lists exactly multiplication, inversion, the action, $g_s$ and the preparation of $|W\rangle$.
--   - generalization: "the preparation of $|W\rangle$ to within negligible error" → $|W_x\rangle$ can be prepared from $x$ in the sense of Definition 3.10 (pure output, a unit ancilla state that may depend on $x$, negligible norm error); reason: the proof's ancilla-free preparation $\|P|0\rangle-|W\rangle\|\le\mu$ is the case of an empty ancilla, so the hypothesis is weaker and the theorem specializes to the source's.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 19, Theorem 4.8 (proof pp. 19–21; Definitions 3.10, 4.3, 4.5 on pp. 13–14, 17–18)

import Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_ConditionH
import Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_PathSuccess
import Definitions.Def_InvariantMoneySecurity_Decomposition_SecurityAssumptions
set_option autoImplicit false

namespace InvariantMoneySecurity.Decomposition.Supplement

open InvariantMoneySecurity.Decomposition

/-- Theorem 4.8, p. 19, both parts, with the explicit bounds `1/q(n)` and `1/(3q(n))`.
No rapid mixing, injectivity or efficiency hypothesis beyond condition (H) is assumed. -/
theorem pathfinding_necessity_condition_H (D : Scheme) (G : SeedFamily D)
    (H : ConditionH D G) {o : ℕ → ℕ} (A : PathFinder o)
    (q : Polynomial ℝ) (hq : PositivePolynomial q) :
    ((∀ n, ∀ x ∈ G n, 1 / q.eval (n : ℝ) ≤ successProb D A n x) → OrbitPrepSolvable D G) ∧
    ((∀ N : ℕ, ∃ n ≥ N, 1 / q.eval (n : ℝ) ≤ seedSuccessProb D G A n) →
      (∃ B : D.Forger, ∀ N : ℕ, ∃ n ≥ N, 1 / (3 * q.eval (n : ℝ)) ≤ D.win B n) ∧
      ¬ D.Secure) := by sorry

end InvariantMoneySecurity.Decomposition.Supplement
