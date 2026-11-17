-- Prove2me | Theorems.Thm_LaconicBarrier_Supplement_theorem_6_10
-- name    : LaconicBarrier.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:36:53.679747+00:00
-- url     : https://prove2.me/theorems/f9c276a4-6650-43cd-9ab5-c6e0fa4fc751
-- title:
--   Theorem 6.10 — adaptive SNARG with a $k$-query reduction gives $L\in\mathsf{SIZE}[2^{O(\ell_P)}\mathrm{poly}(T)]$
-- statement:
--   Fix a nondecreasing polynomial $p$ and a security-parameter function $\lambda = \lambda(n)$ with $n \le p(\lambda(n))$ for every $n$. Let $L = L_{\mathcal R}$ for an NP relation $\mathcal R$ with witness bound $q$, and let $\Pi = (G, P, V)$ be an adaptively sound SNARG for $\mathcal R$ with proof length $\ell_P(\lambda, n)$. Suppose its adaptive soundness admits a non-uniform, $k(\lambda, n)$-query, $T(\lambda, n)$-time black-box reduction $(\mathcal R, F)$ with adaptive queries to a game-based assumption $(\mathcal C, c)$. The advice $F(1^\lambda, 1^n)$ may be any randomized mapping, with no bound on its description complexity. Assume:
--
--   1. $(\mathcal C, c)$ is secure against $\mathcal R \circ P$ at the reduction's target-parameter map $f$ (Definition 6.1, adaptive form);
--   2. the standing assumptions: $\lambda(\cdot), T, k, \ell_P$ are time-constructible and $c$ is efficiently computable.
--
--   Then, writing $\lambda = \lambda(n)$,
--   $$
--   L \in \mathsf{SIZE}\Bigl[2^{O(\ell_P(\lambda, n))} \cdot \mathrm{poly}\bigl(T(\lambda, n)\bigr)\Bigr].
--   $$
--
--   This extends the barrier for adaptively sound SNARGs from one-query reductions (Corollary 6.9) to reductions making many adaptive queries, with advice of any description complexity, following the argument of Gentry and Wichs.
--
--   **Formalization Note** $2^{O(\ell_P)}\cdot\mathrm{poly}(T)$ is $2^{a\,\ell_P(\lambda(n), n)}\,(T(\lambda(n), n) + 2)^c$ for constants $a, c$ and every $n$; small lengths are absorbed by the constants. A reduction with adaptive queries is the mission's general `Reduction`.
--
--   Differences from the source:
--   - generalization: adaptively sound SNARG (Definition 4.7: completeness, succinctness, adaptive soundness) → polynomial-time (G, P, V) with the completeness of Definition 4.7 and the explicit length bounds; adaptive soundness and succinctness are not hypotheses; reason: the proof uses neither (succinctness only through ℓ_P, soundness only through the reduction guarantee); every adaptively sound SNARG satisfies the Lean hypotheses
--   - encoding: negligible completeness error κ(λ) for every polynomial p → for every K > 0, for all large λ, acceptance ≥ 1 − λ^(−K) on every (x, w) ∈ R with |x| ≤ p(λ), |w| ≤ q(|x|); reason: equivalent: finitely many pairs per λ
--   - encoding: adaptive-soundness game C_{1^n}: receive (x, π) → SNARG.adaptiveSource: the response is the tuple code tup [x, π], other strings lose; index set {1^n}; reason: one-string replies in the published two-message game family; tup is injective
--   - reading: black-box reduction to a game-based assumption (C, c) → IsBBReduction with Γ(λ, n) = λ (Definition 4.13); reason: p.37: 'For a reduction to (C, c) (Definition 4.13), we apply the lemma with Γ(λ, n) = λ'
--   - reading: ℓ_P(λ, n) bounds the proof length → every honest proof P(pk, x, w) with pk from G(1^λ, 1^{|x|}) and |w| ≤ q(|x|) has length ≤ ℓ_P(λ, |x|); reason: §6, p.37: 'ℓ_P(λ, n) bounds the prover-message length over all witnesses of length at most q(n)'
--   - encoding: (C, c) is secure against R ∘ P at f (Definition 6.1), adaptive form → SecureHonestAd with k(λ, n) pairs and Γ = T; reason: Definition 6.1
--   - generalization: T-time reduction: one target-game execution, including f and the challenger at λ′, takes at most T(λ,|x|) steps → the published Reduction.IsTTime: each step of the reduction, the challenger at λ′ and f computable within (T+2)^c steps, with at most (T+2)^c coins and actions; reason: every strict T-time reduction satisfies it; the paper's arguments use only that the execution is simulable in poly(T) (p.21)
--   - encoding: at most k oracle calls in one target-game execution → the published Reduction.IsKQuery: no query on any view (reachable or not) holding k replies; reason: a reduction can be modified on unreachable views without changing any execution
--   - encoding: non-uniform reduction with adaptive queries and any randomized advice F(1^λ, 1^n) → the published Reduction (adaptive queries are its general case) and any F with |z| ≤ T(λ, n) on the support (AdviceBounded on {1^n}); reason: §4.1.6, p.20: advice bounded by T; no description bound is stated
--   - encoding: L ∈ SIZE[2^{O(ℓ_P(λ,n))} · poly(T(λ, n))] → ∃ a c, ∀ n, a circuit with at most 2^{a·ℓ_P(λ(n), n)}·(T(λ(n), n) + 2)^c gates decides L on {0,1}^n; reason: constants independent of n; the poly convention of the mission
--   - reading: standing assumptions (p.15): resource bounds time-constructible, baselines and error bounds efficiently computable, 'we do not repeat these conditions' → explicit hypotheses TimeConstr / EffComputable / EffReal on the bounds and constants the statement uses; reason: the paper's own convention, applied as in the published theorem_6_3
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 6.10, p.45 (PDF 48); restated with proof in App. A.4, p.75 (PDF 78)

import Mathlib
import Definitions.Def_LaconicBarrier_Lang
import Definitions.Def_LaconicBarrier_Supplement_SNARG
import Definitions.Def_LaconicBarrier_Supplement_SecureHonestAd
import Definitions.Def_LaconicBarrier_Supplement_SizeAtMost
import Definitions.Def_LaconicBarrier_IsBBReduction
import Definitions.Def_LaconicBarrier_Reduction_IsTTime
import Definitions.Def_LaconicBarrier_Reduction_IsKQuery
import Definitions.Def_LaconicBarrier_AdviceBounded
import Definitions.Def_LaconicBarrier_TimeConstr
import Definitions.Def_LaconicBarrier_EffComputable

namespace LaconicBarrier.Supplement

/-- **Theorem 6.10** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for
Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 6.10, p.45;
restated with proof in App. A.4, p.75): adaptive soundness with a multi-query reduction gives small
circuits. Fix a nondecreasing polynomial `p` and `λ = λ(n)` with `n ≤ p(λ(n))`. Let `L = L_R` have an
adaptively sound SNARG `Π = (G, P, V)` with proof length `ℓ_P(λ, n)`, whose soundness admits a
non-uniform, `k(λ, n)`-query, `T(λ, n)`-time black-box reduction `(R, F)` with adaptive queries to
`(C, c)`, and assume `(C, c)` is secure against `R ∘ P` at `f` (Definition 6.1, adaptive form). Then,
with `λ = λ(n)`, `L ∈ SIZE[2^{O(ℓ_P(λ,n))} · poly(T(λ, n))]`.

**Formalization Note** `2^{O(ℓ_P)} · poly(T)` is `2^{a·ℓ_P} · (T + 2)^c` for constants `a, c`, for
every `n` (no threshold: finitely many small lengths are absorbed by the constants). "Adaptive
queries" is the general published `Reduction`; the advice `F(1^λ, 1ⁿ)` is any randomized mapping
bounded by `T` (no description-complexity bound). "A reduction to `(C, c)`" is Definition 4.13 with
`Γ(λ, n) = λ`, from the adaptive-soundness game. "Adaptively sound SNARG" enters through polynomial
time, completeness and the proof-length bound (see the differences list). The standing assumptions
(§4.1.1, p.15) are hypotheses: `λ(·), T, k, ℓ_P` time-constructible and `c` efficiently
computable. -/
theorem theorem_6_10 (p : Polynomial ℕ) (hp : Monotone p.eval) (lamF : ℕ → ℕ)
    (hlam : ∀ n, n ≤ p.eval (lamF n))
    (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ) (hRel : IsNPRel Rel q)
    (S : SNARG) (hS : S.IsPPT) (hSc : S.Complete Rel q) (ℓP : ℕ → ℕ → ℕ)
    (hℓP : ∀ (lam : ℕ) (x w : List Bool) (ρ : Fin (S.gcoins lam x.length) → Bool)
      (ρ' : Fin (S.pcoins (S.G lam x.length ρ).1 x w) → Bool), w.length ≤ q.eval x.length →
      (S.P (S.G lam x.length ρ).1 x w ρ').length ≤ ℓP lam x.length)
    (R : Reduction) (F : ℕ → List Bool → PMF (List Bool)) (G : Game) (T k : ℕ → ℕ → ℕ)
    (hT : ∀ lam n, lam + n ≤ T lam n) (hTime : R.IsTTime G T)
    (hAdv : AdviceBounded F unaryIdx T) (hK : R.IsKQuery k)
    (hRed : IsBBReduction (S.adaptiveSource Rel) unaryIdx R F G (fun lam _ => lam))
    (hlamc : TimeConstr (fun n => [unary n]) lamF)
    (hTc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => T a.1 a.2))
    (hkc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => k a.1 a.2))
    (hℓPc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => ℓP a.1 a.2))
    (hcc : EffReal G.c)
    (dummy : List Bool) (hSec : SecureHonestAd G S Rel q.eval R k T dummy p.eval T) :
    ∃ a c : ℕ, InSIZE (Lang Rel)
      (fun n => 2 ^ (a * ℓP (lamF n) n) * (T (lamF n) n + 2) ^ c) := by sorry

end LaconicBarrier.Supplement
