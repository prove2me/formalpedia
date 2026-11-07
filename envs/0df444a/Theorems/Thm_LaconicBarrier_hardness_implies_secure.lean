-- Prove2me | Theorems.Thm_LaconicBarrier_hardness_implies_secure
-- name    : LaconicBarrier.hardness_implies_secure
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:47:27.568199+00:00
-- url     : https://prove2.me/theorems/627bc739-f6ed-44a0-bcbf-f47603890ccc
-- title:
--   §6 after Definition 6.1 — $T$-hardness at $f$ implies security against $\mathcal R \circ \mathcal P$
-- statement:
--   Let $\Pi = (\mathcal V, \mathcal P)$ be a polynomial-time two-message argument for an NP relation $\mathcal R$ with witness bound $q$, let $\mathcal R$ be a $k$-query, $T$-time reduction ($T(\lambda,n) \ge \lambda + n$) run against $(\mathcal C, c)$, and suppose $(\mathcal C, c)$ is $T$-hard at the reduction's target-parameter map $f$ for index lengths $n \le p(\lambda)$, $p$ a polynomial. Then $(\mathcal C, c)$ is secure against the honest-prover reduction $\mathcal R \circ \mathcal P$ at $f$ (Definition 6.1), for the same $p$ and for every choice of the dummy response.
--
--   The reason is that $\mathcal R \circ \mathcal P$ is computed by circuits of size $\mathrm{poly}(T(\lambda, n))$, which the hardness hypothesis covers; this is how the corollaries obtain the security hypothesis of Lemma 6.2 and Theorem 6.3.
--
--   Differences from the source:
--   - reading: secure against R∘P with 'a fixed dummy response' → for every dummy response; reason: the conclusion does not depend on the choice
--   - encoding: Definition 4.14: every sequence (n_λ, aux_λ) with n_λ ≤ p(λ), aux_λ allowed, for every λ → sequences required to satisfy the constraints for all sufficiently large λ; reason: breaking is an infinitely-often property; identical whenever every allowed set is nonempty, as for R∘P
--   - encoding: a polynomial p with δ(λ) > 1/p(Γ(λ)) infinitely often → δ(λ) > (Γ(λ)+2)^(−e) for some e ∈ ℕ, infinitely often; reason: every positive polynomial is at most (t+2)^e; avoids 1/p = 1/0 = 0
--   - encoding: non-uniform (probabilistic) adversary circuits of size |A_λ| ≤ Γ(λ) → deterministic multi-output circuits computing each reply from the padded code of the transcript; size = gates + outputs; reason: fixing the best coins never lowers the winning probability or raises the size; other size measures differ polynomially, which T-hardness (every K) absorbs
--   - encoding: probabilistic challenger with any number of rounds → coins and number of actions bounded at each λ; the challenger speaks first; running out of actions is lose; reason: at the target parameters the T-time bound bounds both; elsewhere the game is never run
--   - generalization: T-time reduction: one target-game execution, including f and the challenger at λ′, takes at most T(λ,|x|) steps → each step of the reduction, the challenger at λ′ = f(1^λ, n) and f computable within (T+2)^c steps, with at most (T+2)^c coins and actions, for one constant c; reason: every strict T-time reduction satisfies this; the paper's arguments use only that the execution is simulable in poly(T) (p.21)
--   - encoding: at most k oracle calls in one target-game execution → no query on any view (reachable or not) that already holds k replies; reason: a reduction can be modified on unreachable views without changing any execution
--   - encoding: NP relation: polynomial-time decidable, witness bound q → IsNPRel: the published PolyPred2 (one-tape CookPvsNP machines on x#w) and |w| ≤ q(|x|) for a polynomial q; reason: same class of relations and languages
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §6, after Definition 6.1, p.37 (PDF p.40)

import Mathlib
import Definitions.Def_LaconicBarrier_Lang
import Definitions.Def_LaconicBarrier_LaconicArg
import Definitions.Def_LaconicBarrier_SecureHonest
import Definitions.Def_LaconicBarrier_THardAt
import Definitions.Def_LaconicBarrier_Reduction_IsTTime
import Definitions.Def_LaconicBarrier_Reduction_IsKQuery

namespace LaconicBarrier

/-- **Hardness implies security against `R ∘ P`** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), §6 after Definition 6.1, p.37: "Since
`R ∘ P` is computed by circuits of size `poly(T(λ, n))`, `T`-hardness at `f` (Definition 4.12)
implies security against `R ∘ P` at `f`"). Let `Π = (V, P)` be a polynomial-time two-message
argument for an NP relation `R` with witness bound `q`, let `R` be a `k`-query `T`-time reduction
(`T(λ, n) ≥ λ + n`) run against `(C, c)`, and let `(C, c)` be `T`-hard at the reduction's
target-parameter map for index lengths `n ≤ p(λ)`. Then `(C, c)` is `T`-secure against `R ∘ P` at
`f` for the same `p`, whatever the dummy response. -/
theorem hardness_implies_secure (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ)
    (hRel : IsNPRel Rel q) (A : LaconicArg) (hA : A.IsPPT) (R : Reduction) (G : Game)
    (T k : ℕ → ℕ → ℕ) (hT : ∀ lam n, lam + n ≤ T lam n) (hTime : R.IsTTime G T)
    (hk : R.IsKQuery k) (p : Polynomial ℕ) (hHard : THardAt G T R.f p.eval)
    (dummy : List Bool) :
    SecureHonest G A Rel q.eval R k T dummy p.eval T := by sorry

end LaconicBarrier
