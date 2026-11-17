-- Prove2me | Theorems.Thm_LaconicBarrier_Supplement_theorem_8_3
-- name    : LaconicBarrier.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:38:13.883202+00:00
-- url     : https://prove2.me/theorems/e09bb207-e5b0-4680-b8bb-f62a4d0d8418
-- title:
--   Theorem 8.3 — a multi-query reduction gives an MIP with strong local correctness
-- statement:
--   Fix a nondecreasing polynomial $p$ and a security-parameter function $\lambda = \lambda(n)$ with $n \le p(\lambda(n))$ for every $n$. Let $L = L_{\mathcal R}$ for an NP relation $\mathcal R$ with witness bound $q$, and let $\Pi = (\mathcal V_1, \mathcal V_2, \mathcal P)$ be a two-message laconic argument for $\mathcal R$ with soundness baseline $c_0$, verifier-message length $\ell_V(\lambda, n)$ and prover-message length $\ell_P(\lambda, n)$. Suppose its non-adaptive soundness admits a non-uniform, $k(\lambda,n)$-query, $T(\lambda, n)$-time black-box reduction $(\mathcal R, F)$ with deterministic advice $F(1^\lambda, x)$ to the $\Gamma$-hardness of $(\mathcal C, c)$ at its target-parameter map $f$, where
--   $$
--   \lambda \le \Gamma(\lambda, n) \le T(\lambda, n), \qquad 1 \le k(\lambda, n) \le T(\lambda, n).
--   $$
--   Assume:
--
--   1. the completeness error $\kappa$ of $\Pi$ satisfies $\kappa(\lambda, n) \le \Gamma(\lambda, n)^{-K}$ for every constant $K > 0$, all sufficiently large $\lambda$ and all $n \le p(\lambda)$;
--   2. $(\mathcal C, c)$ is secure against $\mathcal R \circ \mathcal P$ at $f$ (Definition 6.1); this holds whenever $(\mathcal C, c)$ is $T$-hard at $f$;
--   3. the standing assumptions: $\lambda(\cdot), T, \Gamma, k, \ell_P, \ell_V$ time-constructible, $c, c_0$ efficiently computable.
--
--   Define the promise problem
--   $$
--   L^F_{\mathrm{yes}} = \{(1^\lambda, x, z) : x \in L,\ |z| \le T(\lambda, n)\}, \qquad L^F_{\mathrm{no}} = \{(1^\lambda, x, F(1^\lambda, x)) : x \notin L\},
--   $$
--   with $n = |x|$ and $\lambda = \lambda(n)$. Then there are a prover bound $k'(\lambda, n) \le k(\lambda, n)^2\,\mathrm{poly}(\Gamma(\lambda, n))$ and efficiently computable error bounds with $1 - \epsilon_c(n) - \epsilon_s(n) \ge 1/\mathrm{poly}(\Gamma(\lambda, n))$ such that:
--
--   1. $(L^F_{\mathrm{yes}}, L^F_{\mathrm{no}}) \in \mathsf{MIP}\bigl(\text{provers} = k',\ \text{verifier time} = \mathrm{poly}(T),\ \text{ind prover comm} = \ell_P,\ \text{verifier comm} = k\,\ell_V,\ \text{completeness} \ge 1 - \epsilon_c,\ \text{soundness} \le \epsilon_s\bigr)$ with a uniform verifier;
--   2. the verifier contacts at most $k(\lambda, n)$ distinct provers;
--   3. strong local correctness: for every $x \in L$, every allowed $z$ and every tuple $(w_1, \dots, w_{k'})$ with $(x, w_i) \in \mathcal R$, the specified honest provers are accepted with probability at least $1 - \epsilon_c(n)$;
--   4. each honest prover runs in polynomial time given its own witness;
--   5. if the reduction's queries are non-adaptive, the protocol is non-adaptive.
--
--   Resource bounds are in terms of $n = |x|$, while the common input is $(1^\lambda, x, z)$.
--
--   Multi-query reductions thus give multiprover proofs rather than single-prover ones; the strong local correctness lets honest provers hold different witnesses.
--
--   **Formalization Note** The common input is the pair $(x, z)$ encoded as $(1^{\lambda(|x|)}, x, z)$. The deterministic advice is a function $F$, used as a point mass in the published reduction notions. Verifier randomness is the default $O(\text{verifier time})$. The honest provers are one algorithm $H(x, w, q; \rho)$ that reads neither $z$ nor its index.
--
--   Differences from the source:
--   - generalization: a two-message laconic argument (Definition 4.6: negligible completeness, succinctness, soundness) → polynomial-time algorithms (V₁, P, V₂) with message bounds ℓ_V, ℓ_P and only the stated completeness hypothesis on κ; reason: the proof uses neither soundness nor succinctness; every laconic argument satisfies the Lean hypotheses (as in the published theorem_6_3)
--   - encoding: deterministic advice F(1^λ, x) → a function F, used as the point mass δ_{F(1^λ,x)} in IsBBReduction and AdviceBounded; reason: Definition 4.17: F deterministic
--   - generalization: T-time reduction: one target-game execution, including f and the challenger at λ′, takes at most T(λ,|x|) steps → the published Reduction.IsTTime: each step of the reduction, the challenger at λ′ and f computable within (T+2)^c steps, with at most (T+2)^c coins and actions; reason: every strict T-time reduction satisfies it; the paper's arguments use only that the execution is simulable in poly(T) (p.21)
--   - encoding: at most k oracle calls in one target-game execution → the published Reduction.IsKQuery: no query on any view (reachable or not) holding k replies; reason: a reduction can be modified on unreachable views without changing any execution
--   - encoding: every real constant K > 0 → every K ∈ ℕ, K > 0; reason: Γ ≥ λ ≥ 1 for large λ, so the bound for ⌈K⌉ implies the one for K
--   - encoding: the promise problem on triples (1^λ, x, z), λ = λ(|x|) → pairs (x, z) encoded as (1^{λ(|x|)}, x, z); reason: λ is determined by |x|
--   - encoding: (L^F_yes, L^F_no) ∈ MIP(provers = k′, verifier time = poly(T), ind prover comm = ℓ_P, verifier comm = kℓ_V, …) (Definition 4.32; randomness omitted) → MIPVerifier.Proves with per-action time (T+2)^d, randomness C·((T+2)^d+1), questions only to provers j < k′, each at most once, total questions ≤ k·ℓ_V, replies ≤ ℓ_P bits; reason: the class of p.28 with the default O(verifier time) randomness; at most k+1 actions, so per-action and total polynomial time agree up to a polynomial
--   - encoding: soundness against unbounded noncommunicating provers that may share randomness and agree on non-uniform strategies → soundness against every tuple of reply distributions with independent coins; reason: shared randomness gives mixtures of deterministic tuples, which are covered; acceptance is linear in the mixture
--   - encoding: k′(λ, n) ≤ k(λ, n)² poly(Γ(λ, n)); 1 − ϵ_c(n) − ϵ_s(n) ≥ 1/poly(Γ(λ, n)) → k′ ≤ k²·(Γ + 2)^d and gap ≥ (Γ(λ(n), n) + 2)^(−e); reason: the poly convention of the mission
--   - reading: the verifier contacts at most k(λ, n) distinct provers → on every consistent transcript the verifier asks a question only while fewer than k(λ(n), n) questions have been asked; reason: each prover is asked at most once, so questions and contacted provers are counted alike
--   - encoding: strong local correctness (Definition 8.1) for every x ∈ L, every allowed z and every tuple (w_1, …, w_{k′}) with (x, w_i) ∈ R → MIPVerifier.StrongLocal on the yes-instances with honest provers H(x, w_j, question; independent coins); reason: Definition 8.1
--   - generalization: specified honest provers P_1, …, P_{k′} → one honest algorithm H for every prover index, reading neither z nor its index; reason: a stronger conclusion: the paper's honest provers all return P(pk, x, w_i) and ignore z (p.53)
--   - reading: each honest prover runs in time poly(λ, n) given its own witness → coins and running time of H on (1^{λ(n)}, x, w, question, coins) at most (λ(n) + n + |question| + 2)^d for every witness of length ≤ q(n), by one machine; reason: the honest prover answers a question pk of the protocol, whose length is the verifier-message length ℓ_V(λ, n), polynomial in (λ, n) for a polynomial-time Π; the bound in the question length is poly(λ, n) on such questions
--   - encoding: if the reduction's queries are non-adaptive (Definition 4.21), the protocol is non-adaptive (Remark after Definition 4.32) → NonAdaptiveQueries R → V.IsNonAdaptive; reason: both definitions fix the content of the t-th query (and, for the protocol, its recipient) from the view before the first reply (the coins) and let the run stop early; as with IsKQuery, the condition on the reduction is over every view, reachable or not, and a reduction can be modified on unreachable views without changing any execution
--   - reading: there exist completeness and soundness error bounds (standing assumption: error bounds efficiently computable) → the error bounds produced lie in [0, 1] and are efficiently computable; reason: the standing assumption applies to the error bounds the theorem produces, as in the published theorem_6_3
--   - reading: standing assumptions (p.15): resource bounds time-constructible, baselines and error bounds efficiently computable, 'we do not repeat these conditions' → explicit hypotheses TimeConstr / EffComputable / EffReal on the bounds and constants the statement uses; reason: the paper's own convention, applied as in the published theorem_6_3
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 8.3, p.52 (PDF 55); Definitions 4.21, 4.32, 8.1, 6.1

import Mathlib
import Definitions.Def_LaconicBarrier_Lang
import Definitions.Def_LaconicBarrier_LaconicArg_source
import Definitions.Def_LaconicBarrier_SecureHonest
import Definitions.Def_LaconicBarrier_IsBBReduction
import Definitions.Def_LaconicBarrier_Reduction_IsTTime
import Definitions.Def_LaconicBarrier_Reduction_IsKQuery
import Definitions.Def_LaconicBarrier_AdviceBounded
import Definitions.Def_LaconicBarrier_TimeConstr
import Definitions.Def_LaconicBarrier_EffComputable
import Definitions.Def_LaconicBarrier_Supplement_NonAdaptiveQueries
import Definitions.Def_LaconicBarrier_Supplement_InMIP
import Definitions.Def_LaconicBarrier_Supplement_StrongLocal

namespace LaconicBarrier.Supplement

/-- **Theorem 8.3** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for
Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 8.3, p.52):
from a multi-query reduction to a multiprover interactive proof. Fix a nondecreasing polynomial `p`
and `λ = λ(n)` with `n ≤ p(λ(n))`. Let `L = L_R` have a two-message laconic argument
`Π = (V₁, V₂, P)` with soundness baseline `c₀`, verifier-message length `ℓ_V(λ, n)` and
prover-message length `ℓ_P(λ, n)`. Let its non-adaptive soundness admit a non-uniform,
`k(λ, n)`-query, `T(λ, n)`-time black-box reduction `(R, F)` with deterministic advice `F(1^λ, x)` to
the Γ-hardness of `(C, c)` at its target-parameter map, `λ ≤ Γ ≤ T`, `1 ≤ k ≤ T`. Assume the
completeness error `κ` of `Π` satisfies `κ(λ, n) ≤ Γ(λ, n)^{−K}` for every `K > 0`, all large `λ` and
all `n ≤ p(λ)`, and that `(C, c)` is secure against `R ∘ P` at `f`. Let
`L^F_yes = {(1^λ, x, z) : x ∈ L, |z| ≤ T(λ, n)}`, `L^F_no = {(1^λ, x, F(1^λ, x)) : x ∉ L}`,
`λ = λ(|x|)`. Then there are `k′(λ, n) ≤ k(λ, n)² poly(Γ(λ, n))` and errors with
`1 − ϵ_c(n) − ϵ_s(n) ≥ 1/poly(Γ(λ, n))` such that `(L^F_yes, L^F_no) ∈ MIP(provers = k′, verifier time =
poly(T), ind prover comm = ℓ_P, verifier comm = k·ℓ_V, completeness ≥ 1 − ϵ_c, soundness ≤ ϵ_s)`; the
verifier is uniform and contacts at most `k(λ, n)` distinct provers; the protocol has strong local
correctness with specified honest provers, each running in polynomial time given its own witness;
and if the reduction's queries are non-adaptive, the protocol is non-adaptive.

**Formalization Note** The common input is the pair `(x, z)`, encoded as `(1^{λ(|x|)}, x, z)`. The
deterministic advice is a function `F` used as the point mass `δ_{F(1^λ, x)}` in the published
reduction notions. Verifier randomness is the default `O(verifier time)`. The honest provers are one
algorithm `H(x, w, q; ρ)` (the prover index is not an input), whose time is bounded by a polynomial in
`λ(n)`, `n` and the length of the question it answers. The remark "this holds whenever `(C, c)` is
`T`-hard at `f`" is the published `hardness_implies_secure`, not a hypothesis. The standing
assumptions (§4.1.1, p.15) are hypotheses: `λ(·), T, Γ, k, ℓ_P, ℓ_V` time-constructible, `c, c₀`
efficiently computable; the error bounds produced are efficiently computable. -/
theorem theorem_8_3 (p : Polynomial ℕ) (hp : Monotone p.eval) (lamF : ℕ → ℕ)
    (hlam : ∀ n, n ≤ p.eval (lamF n))
    (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ) (hRel : IsNPRel Rel q)
    (A : LaconicArg) (hA : A.IsPPT) (c₀ : ℝ) (h0 : 0 ≤ c₀) (h1 : c₀ < 1) (ℓV ℓP : ℕ → ℕ → ℕ)
    (hℓV : ∀ (lam : ℕ) (x : List Bool) (ρ : Fin (A.vcoins lam x) → Bool),
      (A.V1 lam x ρ).1.length ≤ ℓV lam x.length)
    (hℓP : ∀ (lam : ℕ) (x w : List Bool) (ρ : Fin (A.vcoins lam x) → Bool)
      (ρ' : Fin (A.pcoins (A.V1 lam x ρ).1 x w) → Bool), w.length ≤ q.eval x.length →
      (A.P (A.V1 lam x ρ).1 x w ρ').length ≤ ℓP lam x.length)
    (R : Reduction) (F : ℕ → List Bool → List Bool) (G : Game) (T Γ k : ℕ → ℕ → ℕ)
    (hT : ∀ lam n, lam + n ≤ T lam n) (hTime : R.IsTTime G T)
    (hAdv : AdviceBounded (fun lam x => PMF.pure (F lam x)) (Lang Rel)ᶜ T)
    (hK : R.IsKQuery k) (hk : ∀ lam n, 1 ≤ k lam n ∧ k lam n ≤ T lam n)
    (hΓ : ∀ lam n, lam ≤ Γ lam n ∧ Γ lam n ≤ T lam n)
    (hRed : IsBBReduction (A.source c₀ h0 h1) (Lang Rel)ᶜ R (fun lam x => PMF.pure (F lam x)) G Γ)
    (hκ : ∀ K : ℕ, 0 < K → ∀ᶠ lam : ℕ in Filter.atTop, ∀ x w : List Bool,
      x.length ≤ p.eval lam → w.length ≤ q.eval x.length → Rel x w →
      1 - (((Γ lam x.length : ℕ) : ℝ) ^ K)⁻¹ ≤ A.honestAcc lam x w)
    (hlamc : TimeConstr (fun n => [unary n]) lamF)
    (hTc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => T a.1 a.2))
    (hΓc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => Γ a.1 a.2))
    (hkc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => k a.1 a.2))
    (hℓPc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => ℓP a.1 a.2))
    (hℓVc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => ℓV a.1 a.2))
    (hcc : EffReal G.c) (hc0c : EffReal c₀)
    (dummy : List Bool) (hSec : SecureHonest G A Rel q.eval R k T dummy p.eval T) :
    ∃ (kP : ℕ → ℕ → ℕ) (εc εs : ℕ → ℝ) (d e C : ℕ),
      (∀ lam n, kP lam n ≤ k lam n ^ 2 * (Γ lam n + 2) ^ d) ∧
      (∀ n, εc n ∈ Set.Icc (0 : ℝ) 1 ∧ εs n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, ((((Γ (lamF n) n : ℕ) : ℝ) + 2) ^ e)⁻¹ ≤ 1 - εc n - εs n) ∧
      EffComputable (fun n => [unary n]) εc (fun n => (T (lamF n) n + 2) ^ d) ∧
      EffComputable (fun n => [unary n]) εs (fun n => (T (lamF n) n + 2) ^ d) ∧
      ∃ V : MIPVerifier (List Bool × List Bool),
        V.Proves (fun i => [unary (lamF i.1.length), i.1, i.2])
          {i | i.1 ∈ Lang Rel ∧ i.2.length ≤ T (lamF i.1.length) i.1.length}
          {i | i.1 ∉ Lang Rel ∧ i.2 = F (lamF i.1.length) i.1}
          (fun i => kP (lamF i.1.length) i.1.length)
          (fun i => (T (lamF i.1.length) i.1.length + 2) ^ d)
          (fun i => ℓP (lamF i.1.length) i.1.length)
          (fun i => k (lamF i.1.length) i.1.length * ℓV (lamF i.1.length) i.1.length)
          (fun i => C * ((T (lamF i.1.length) i.1.length + 2) ^ d + 1))
          (fun i => εc i.1.length) (fun i => εs i.1.length) ∧
        (∀ (i : List Bool × List Bool) (ρ : Fin (V.coins i) → Bool)
          (h : List (ℕ × List Bool × List Bool)) (j : ℕ) (qq : List Bool),
            V.Consistent i ρ h → V.next i ρ h = .ask j qq →
              h.length < k (lamF i.1.length) i.1.length) ∧
        (∃ (hc : List Bool → List Bool → List Bool → ℕ)
          (H : (x w qq : List Bool) → (Fin (hc x w qq) → Bool) → List Bool)
          (M : KarpLiptonOM.OracleTM),
            (∀ x w qq : List Bool, w.length ≤ q.eval x.length →
              hc x w qq ≤ (lamF x.length + x.length + qq.length + 2) ^ d ∧
              ∀ ρ : Fin (hc x w qq) → Bool,
                RunsWithin M [unary (lamF x.length), x, w, qq, bits ρ] (H x w qq ρ)
                  ((lamF x.length + x.length + qq.length + 2) ^ d)) ∧
            V.StrongLocal {i | i.1 ∈ Lang Rel ∧ i.2.length ≤ T (lamF i.1.length) i.1.length}
              Prod.fst Rel (fun i => kP (lamF i.1.length) i.1.length)
              (fun i => ℓP (lamF i.1.length) i.1.length) hc H (fun i => εc i.1.length)) ∧
        (NonAdaptiveQueries R → V.IsNonAdaptive) := by sorry

end LaconicBarrier.Supplement
