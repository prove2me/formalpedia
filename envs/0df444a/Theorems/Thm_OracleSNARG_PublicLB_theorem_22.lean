-- Prove2me | Theorems.Thm_OracleSNARG_PublicLB_theorem_22
-- name    : OracleSNARG.PublicLB.theorem_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:47:32.411416+00:00
-- url     : https://prove2.me/theorems/5bcdc6bb-29d6-4454-8502-32935ce3bf43
-- title:
--   Theorem 22 (= Theorem 2) — no deterministic publicly verifiable SNARG for robust oracle-aided computations with $|\mathrm{crs}|=o(n)$ and $o(q)$ verifier queries
-- statement:
--   Consider the majority computation $C^O(x)=\mathrm{Maj}(O(x,1),\dots,O(x,N))$ on inputs $x\in\{0,1\}^{n}$. It makes $q=N$ oracle calls, where $n=n(\lambda)$ and $N=N(\lambda)$ are polynomially bounded functions of the security parameter and $N(\lambda)$ is odd for every $\lambda$. Let $\varepsilon\in(0,1/4]$.
--
--   Then there is no scheme $S=(\mathrm{Gen},P,V)$ together with a function $\ell:\mathbb N\to\mathbb N$ such that all of the following hold:
--   - the verifier $V$ is deterministic and public (no private key, no coins), and on every input $(\mathrm{crs},x,\pi)$ it makes at most $\ell(\lambda)$ oracle queries, with $\ell=o(N)$;
--   - every common reference string in the support of $\mathrm{Gen}(1^\lambda)$ has length $|\mathrm{crs}|=o(n)$;
--   - the honest prover $P$ is a polynomial-size randomized oracle algorithm;
--   - adaptive completeness holds;
--   - adaptive soundness for $\varepsilon$-robust computations holds.
--
--   In symbols:
--   $$\neg\,\exists\,(S,\ell):\ \ \mathrm{depth}(V)\le\ell,\ \ \ell=o(N),\ \ |\mathrm{crs}|=o(n),\ \ P\ \text{poly-size},\ \ \text{adaptive completeness},\ \ \text{adaptive }\varepsilon\text{-sound}.$$
--   Both properties are required for every oracle $O:\{0,1\}^*\to\{0,1\}$ fixed independently of setup, against polynomial-size (non-uniform) oracle algorithms; see the definition item `Scheme`. No bound is placed on the proof length.
--
--   This is the paper's lower bound complementing its privately verifiable constructions. With public deterministic verification, short public parameters and a sublinear number of verifier queries, robustness alone does not suffice for soundness, so a private verification key or authenticated (signed) oracle answers is needed.
--
--   Differences from the source:
--
--   - generalization: SNARG algorithms Gen, V polynomial-time (Definition 9) → Gen any distribution on bit strings without oracle access and V any deterministic oracle procedure of depth ≤ ℓ(λ); reason: non-existence over a larger class of schemes implies the paper's statement
--   - generalization: the honest prover a polynomial-time algorithm → a non-uniform polynomial-size randomized oracle circuit family; reason: non-uniform circuits include polynomial-time machines, so excluding all such schemes implies the paper's statement
--   - generalization: "a SNARG … for robust oracle-aided computations" → no scheme exists already for the single majority computation C^O(x) = Maj(O(x,1), …, O(x,N)), for every polynomially bounded n, N with N odd; reason: a SNARG for robust oracle-aided computations in general yields one for this computation, which is the paper's own witness (Theorem 2: "already holds for the simple computation …")
--   - reading: "robust" with unspecified ε → every ε ∈ (0, 1/4]; reason: the proof produces 1/4-robust false statements; for ε > 1/2 and N(λ) → ∞ no false statement is ε-robust at large λ, soundness is vacuous and the always-accepting verifier is a scheme, so the reading for all ε ∈ (0, 1] is false
--   - encoding: purported executions of C^O → answer vectors a ∈ {0,1}^N with q(τ) = N; reason: the computation's queries are fixed, so purported executions are exactly answer vectors
--   - encoding: queries (x, i), i ∈ [N] → the bit string 1^i 0 x with i = 0, …, N − 1; reason: a fixed injective pair encoding, which the paper leaves unspecified
--   - encoding: completeness (non-adaptive and adaptive) → adaptive completeness only, with the event |x| = n(λ) ∧ C^O(x) = 1 ∧ V rejects; reason: the non-adaptive clause is the special case of constant choosers
--   - encoding: "the verifier makes o(q) queries" → a decision tree of depth ≤ ℓ(λ) on every input, with ℓ = o(N) as little-o in λ; reason: depth bounds the queries against every oracle, and q = N
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 24, Theorem 22 (informal Theorem 2, p. 3); Definitions 9 (p. 13), 15-17 (pp. 16-17)

import Mathlib
import Definitions.Def_OWFLocalDesc_Negligible
import Definitions.Def_OracleSNARG_PublicLB_Majority
import Definitions.Def_OracleSNARG_PublicLB_Algorithms
import Definitions.Def_OracleSNARG_PublicLB_Scheme

set_option autoImplicit false

namespace OracleSNARG.PublicLB

/-- **Theorem 22** (= Theorem 2). Goldwasser, Kalai, *Incrementally Verifiable Oracle Aided
Computation*, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 24: "There does not exist a
SNARG with adaptive completeness and adaptive soundness for robust oracle-aided computations with
deterministic public verification, with |crs| = o(n), where n is the input length, and where the
verifier makes o(q) queries, where q is the number of oracle gates." Stated for the paper's
witness computation `C^O(x) = Maj(O(x,1), …, O(x,N))` on `x ∈ {0,1}^{n(λ)}` (q = N), for all
polynomially bounded `n`, `N` with `N(λ)` odd and every `ε ∈ (0, 1/4]`: no scheme has a
verifier making at most `ℓ(λ) = o(N(λ))` queries on every input, `|crs| = o(n)`, a
polynomial-size honest prover, adaptive completeness and adaptive `ε`-robust soundness. -/
theorem theorem_22 (n N : ℕ → ℕ) (hn : PolyBounded n) (hN : PolyBounded N)
    (hodd : ∀ lam, Odd (N lam)) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 4) :
    ¬ ∃ (S : Scheme) (ℓ : ℕ → ℕ),
      (∀ lam crs x π, (S.verifier lam crs x π).depth ≤ ℓ lam) ∧
      LittleO ℓ N ∧
      CrsLittleO n S ∧
      IsPolySize S.prover ∧
      AdaptiveComplete n N S ∧
      AdaptiveSound n N ε S := by sorry

end OracleSNARG.PublicLB
