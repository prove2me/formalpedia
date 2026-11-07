-- Prove2me | Theorems.Thm_LaconicBarrier_lemma_6_2
-- name    : LaconicBarrier.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:23.610637+00:00
-- url     : https://prove2.me/theorems/01f2b694-6eb0-4fd5-bf46-11d643873c38
-- title:
--   Lemma 6.2 — a common advantage bound for the reduction against strong provers
-- statement:
--   Let $\{(\mathcal D_x, c_0)\}_{x \in X}$ be a family of two-message games, $(\mathcal C, c)$ a game, $\Gamma(\lambda, n) \ge \lambda$ a bound and $(\mathcal R, F)$ a non-uniform black-box reduction from the family to the $\Gamma$-hardness of $(\mathcal C, c)$ at its target-parameter map $f$, with possibly randomized advice of length at most $T(\lambda, |x|)$ on $X$. Fix a nondecreasing polynomial $p$, a constant $\eta \in (0,1]$ and a dummy response, and assume that $(\mathcal C, c)$ is $\Gamma$-secure against $\mathcal R$ run with the oracle that answers every query with the dummy response, on auxiliary inputs $(x, z)$ with $x \in X$, $|x| \le p(\lambda)$, $|z| \le T$.
--
--   Then there is a constant $C$ such that, for all sufficiently large $\lambda$, every $x \in X$ with $|x| \le p(\lambda)$ and every possibly unbounded randomized response oracle $\mathcal P^*$ with advantage at least $\eta$ at $(\lambda, x)$,
--   $$
--   \Pr\bigl[\mathcal R^{\mathcal P^*}(1^\lambda, x, F(1^\lambda, x)) \text{ wins } \mathcal C(1^{f(1^\lambda,|x|)})\bigr] \ge c + \Gamma(\lambda, |x|)^{-C}.
--   $$
--   The constant $C$ and the cutoff depend on $p, \eta, \Gamma$ and the reduction, not on $x$ or $\mathcal P^*$.
--
--   The asymptotic guarantee of the reduction is turned into a uniform, per-instance bound; this is what lets a single verifier use the reduction on every false statement.
--
--   Differences from the source:
--   - generalization: a two-message laconic argument's non-adaptive (X the false statements) or adaptive (X = {1ⁿ}) soundness games; a k-query, T-time reduction → any family of two-message games with any index set X; no query count or time bound, only advice of length ≤ T on X; reason: the proof uses neither; the printed lemma is the special case
--   - generalization: (C, c) Γ-secure against R∘P at f (Definition 6.1) → (C, c) Γ-secure against R run with the oracle answering every query with the fixed dummy response, on auxiliary inputs (x, z) with x ∈ X, |x| = n ≤ p(λ), |z| ≤ T(λ, n); reason: for x ∈ X every witness is invalid (non-adaptive case; invalid pairs in the adaptive case), so R∘P is this algorithm there: the printed hypothesis implies this one, which is all the proof uses
--   - encoding: Definition 4.14: every sequence (n_λ, aux_λ) with n_λ ≤ p(λ), aux_λ allowed, for every λ → sequences required to satisfy the constraints for all sufficiently large λ; reason: breaking is an infinitely-often property; identical whenever every allowed set is nonempty, as for R∘P
--   - encoding: a constant C (real) → C ∈ ℕ; reason: Γ ≥ λ ≥ 1 for large λ, so the bound for ⌈C⌉ is implied by the one for C
--   - encoding: possibly unbounded randomized source adversary, fresh coins on each call → a distribution on strings for each query (PMF), sampled independently on each call; reason: the paper's stateless oracle model, fully general
--   - encoding: a polynomial p with δ(λ) > 1/p(Γ(λ)) infinitely often → δ(λ) > (Γ(λ)+2)^(−e) for some e ∈ ℕ, infinitely often; reason: every positive polynomial is at most (t+2)^e; avoids 1/p = 1/0 = 0
--   - encoding: probabilistic challenger with any number of rounds → coins and number of actions bounded at each λ; the challenger speaks first; running out of actions is lose; reason: at the target parameters the T-time bound bounds both; elsewhere the game is never run
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Lemma 6.2, p.37 (PDF p.40)

import Mathlib
import Definitions.Def_LaconicBarrier_IsBBReduction
import Definitions.Def_LaconicBarrier_AdviceBounded
import Definitions.Def_LaconicBarrier_SecureAgainst

namespace LaconicBarrier

/-- **Lemma 6.2** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Lemma 6.2, p.37): a common advantage bound. Let `(R, F)` be a non-uniform
black-box reduction from a family of two-message games `{(D_x, c₀)}_{x ∈ X}` to the Γ-hardness of
`(C, c)` at its target-parameter map, with `Γ(λ, n) ≥ λ` and advice of length at most `T` on `X`.
Fix a nondecreasing polynomial `p`, a constant `η ∈ (0, 1]` and a dummy response, and assume
`(C, c)` is Γ-secure against `R` run with the dummy oracle (which answers every query with the dummy
response) on auxiliary inputs `(x, z)` with `x ∈ X`, `|z| ≤ T`. Then there is a constant `C` such
that for all sufficiently large `λ`, every `x ∈ X` with `|x| ≤ p(λ)` and every possibly unbounded
randomized response oracle `P*` with advantage at least `η` at `(λ, x)`,
`Pr[R^{P*}(1^λ, x, F(1^λ, x)) wins C(1^{f(1^λ,|x|)})] ≥ c + Γ(λ, |x|)^{−C}`.

**Formalization Note** The paper states the lemma for the soundness games of a two-message argument
(non-adaptive: `X` the false statements; adaptive: `X = {1ⁿ}`), a `k`-query `T`-time reduction,
and security against the honest-prover reduction `R ∘ P`. Its proof uses `R ∘ P` only on indices
in `X` with invalid witnesses, where every query gets the dummy response; that is the hypothesis
here, implied by the printed one. The family, the query count and the time bound are general. -/
theorem lemma_6_2 (S : TwoMsg) (X : Set (List Bool)) (R : Reduction)
    (F : ℕ → List Bool → PMF (List Bool)) (G : Game) (T Γ : ℕ → ℕ → ℕ)
    (hΓ : ∀ lam n, lam ≤ Γ lam n) (hT : ∀ lam n, lam + n ≤ T lam n)
    (hAdv : AdviceBounded F X T) (hRed : IsBBReduction S X R F G Γ)
    (p : Polynomial ℕ) (hp : Monotone p.eval) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (dummy : List Bool)
    (hSec : SecureAgainst (α := List Bool × List Bool) G
      (fun lam a => R.winProb G (fun _ _ => PMF.pure dummy) lam a.1 (PMF.pure a.2))
      (fun lam n => {a | a.1 ∈ X ∧ a.1.length = n ∧ a.2.length ≤ T lam n}) p.eval Γ) :
    ∃ C : ℕ, ∀ᶠ lam : ℕ in Filter.atTop, ∀ x ∈ X, x.length ≤ p.eval lam →
      ∀ O : List Bool → PMF (List Bool), η ≤ S.adv lam x O →
        G.c + (((Γ lam x.length : ℕ) : ℝ) ^ C)⁻¹ ≤ R.winProb G (fun _ => O) lam x (F lam x) := by sorry

end LaconicBarrier
