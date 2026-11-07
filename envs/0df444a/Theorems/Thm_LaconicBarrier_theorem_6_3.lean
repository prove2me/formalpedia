-- Prove2me | Theorems.Thm_LaconicBarrier_theorem_6_3
-- name    : LaconicBarrier.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:39.016174+00:00
-- url     : https://prove2.me/theorems/7856aea8-1fc2-4024-b789-33b0ff845a85
-- title:
--   Theorem 6.3 — a one-query reduction gives a statistically sound one-round proof
-- statement:
--   Fix a nondecreasing polynomial $p$ and a function $\lambda = \lambda(n)$ with $n \le p(\lambda(n))$. Let $L = L_{\mathcal R}$ for an NP relation $\mathcal R$ with witness bound $q$, and let $\Pi = (\mathcal V_1, \mathcal V_2, \mathcal P)$ be a polynomial-time two-message argument for it with soundness baseline $c_0$, verifier-message length $\ell_V(\lambda, n)$ and prover-message length $\ell_P(\lambda, n)$. Suppose its non-adaptive soundness admits a non-uniform, one-query, $T(\lambda,n)$-time black-box reduction $(\mathcal R, F)$, with advice of description complexity $s_F(\lambda, n)$, to the $\Gamma$-hardness of $(\mathcal C, c)$ at its target-parameter map $f$, where $\lambda \le \Gamma(\lambda, n) \le T(\lambda, n)$. Assume:
--
--   1. the completeness error $\kappa$ of $\Pi$ satisfies $\kappa(\lambda, n) \le \Gamma(\lambda, n)^{-K}$ for every $K > 0$, all large $\lambda$ and all $n \le p(\lambda)$;
--   2. $(\mathcal C, c)$ is secure against $\mathcal R \circ \mathcal P$ at $f$;
--   3. the standing assumptions: $\lambda(\cdot), T, \Gamma, s_F, \ell_P, \ell_V$ time-constructible, $c$ and $c_0$ efficiently computable.
--
--   For each $x \notin L$ fix a description $D_{\lambda,x}$ of the advice sampler $\rho \mapsto F(1^\lambda, x; \rho)$ of length at most $s_F(\lambda, n)$, and define the promise problem
--   $$
--   L^F_{\mathrm{yes}} = \{(1^\lambda, x, D) : x \in L,\ |D| \le s_F(\lambda, n)\}, \qquad L^F_{\mathrm{no}} = \{(1^\lambda, x, D_{\lambda,x}) : x \notin L\},
--   $$
--   with $\lambda = \lambda(|x|)$. Then there are efficiently computable error bounds $\epsilon_c, \epsilon_s$ with $1 - \epsilon_c(n) - \epsilon_s(n) \ge 1/\mathrm{poly}(\Gamma(\lambda, n))$ such that
--   $$
--   (L^F_{\mathrm{yes}}, L^F_{\mathrm{no}}) \in \mathsf{IP}\bigl(\text{rounds} = 1,\ \text{verifier time} = \mathrm{poly}(T(\lambda,n), s_F(\lambda,n)),\ \text{prover comm} = \ell_P(\lambda,n),\ \text{verifier comm} = \ell_V(\lambda,n),\ \text{completeness} \ge 1-\epsilon_c,\ \text{soundness} \le \epsilon_s\bigr).
--   $$
--   The verifier is uniform: it reads $D$ as part of its input and uses it to sample the advice.
--
--   This is the paper's main technical step: the argument and its reduction become a statistically sound proof whose verifier mixes the argument's own check with a simulation of the reduction against the target challenger.
--
--   Differences from the source:
--   - generalization: a two-message laconic argument (Definition 4.6: negligible completeness for every p, succinctness, soundness) → polynomial-time algorithms (V₁, P, V₂) with message bounds ℓ_V, ℓ_P and only the stated completeness hypothesis; reason: the proof uses neither soundness nor succinctness (only through ℓ_P); the printed hypotheses imply these
--   - encoding: the promise problem on triples (1^λ, x, D), λ = λ(|x|); 'for each x ∉ L fix D_{λ,x}' → pairs (x, D) encoded as (1^{λ(|x|)}, x, D); the statement holds for every choice x ↦ D_x of descriptions; reason: λ is determined by |x|; 'fix' is a universally quantified choice
--   - encoding: 1 − ϵ_c(n) − ϵ_s(n) ≥ 1/poly(Γ(λ, n)) → ≥ (Γ(λ(n), n) + 2)^(−e) for some e and all n; reason: same notion (Breaks convention)
--   - reading: 'there exist completeness and soundness error bounds' (standing assumption: error bounds efficiently computable) → the error bounds produced lie in [0, 1] and are efficiently computable; reason: the standing assumption applies to the error bounds the theorem produces; the next step (Theorem 5.1) needs them
--   - encoding: every real constant K > 0 → every K ∈ ℕ, K > 0; reason: Γ ≥ λ ≥ 1 for large λ, so the bound for ⌈K⌉ implies the one for K
--   - encoding: verifier communication and randomness omitted (default O(T)) → verifier communication and randomness C·(T+1) for some constant C; reason: the paper's default (p.25)
--   - reading: standing assumptions (p.15): resource bounds time-constructible, baselines and error bounds efficiently computable, 'we do not repeat these conditions' → explicit hypotheses TimeConstr / EffComputable / EffReal on the bounds and constants the statement uses; reason: the paper's own convention; without them a uniform verifier cannot compute its thresholds
--   - reading: baseline c of the target game (and c₀) efficiently computable (standing assumption, p.15) → EffReal: approximable within 1/(N+1) in time poly(N); reason: the paper does not fix the notion; this is the standard one and what the mixed verifier needs
--   - encoding: advice of description complexity s_F (a Boolean-circuit description of r ↦ F(1^λ, x; r)); uniform or non-uniform → a circuit code (MCircuit.code) of length ≤ s_F whose output on uniform input bits, read by unpadOut, has distribution exactly F(1^λ, x); a uniform reduction is the one-gate sampler of the empty string; reason: a fixed, injective, polynomial-time decodable circuit encoding; the uniform case is a special case
--   - generalization: T-time reduction: one target-game execution, including f and the challenger at λ′, takes at most T(λ,|x|) steps → each step of the reduction, the challenger at λ′ = f(1^λ, n) and f computable within (T+2)^c steps, with at most (T+2)^c coins and actions, for one constant c; reason: every strict T-time reduction satisfies this; the paper's arguments use only that the execution is simulable in poly(T) (p.21)
--   - encoding: at most k oracle calls in one target-game execution → no query on any view (reachable or not) that already holds k replies; reason: a reduction can be modified on unreachable views without changing any execution
--   - encoding: a polynomial p with δ(λ) > 1/p(Γ(λ)) infinitely often → δ(λ) > (Γ(λ)+2)^(−e) for some e ∈ ℕ, infinitely often; reason: every positive polynomial is at most (t+2)^e; avoids 1/p = 1/0 = 0
--   - encoding: possibly unbounded randomized source adversary, fresh coins on each call → a distribution on strings for each query (PMF), sampled independently on each call; reason: the paper's stateless oracle model, fully general
--   - encoding: probabilistic challenger with any number of rounds → coins and number of actions bounded at each λ; the challenger speaks first; running out of actions is lose; reason: at the target parameters the T-time bound bounds both; elsewhere the game is never run
--   - encoding: IP / AM classes with verifier time O(T) and communication bounds 'for every prover strategy' → verifier time per verifier step (computed from the transcript) at most C·(T+1); deterministic provers; transcripts over the prover budget rejected; reason: for at most two rounds the per-step and total times agree up to a constant; the best coins of a randomized prover do as well
--   - encoding: NP relation: polynomial-time decidable, witness bound q → IsNPRel: the published PolyPred2 (one-tape CookPvsNP machines on x#w) and |w| ≤ q(|x|) for a polynomial q; reason: same class of relations and languages
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 6.3, pp.38–39 (PDF pp.41–42)

import Mathlib
import Definitions.Def_LaconicBarrier_Lang
import Definitions.Def_LaconicBarrier_LaconicArg_source
import Definitions.Def_LaconicBarrier_SecureHonest
import Definitions.Def_LaconicBarrier_IsBBReduction
import Definitions.Def_LaconicBarrier_Reduction_IsTTime
import Definitions.Def_LaconicBarrier_Reduction_IsKQuery
import Definitions.Def_LaconicBarrier_AdviceBounded
import Definitions.Def_LaconicBarrier_HasDescription
import Definitions.Def_LaconicBarrier_TimeConstr
import Definitions.Def_LaconicBarrier_EffComputable
import Definitions.Def_LaconicBarrier_InIP

namespace LaconicBarrier

/-- **Theorem 6.3** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 6.3, pp.38–39): from a one-query reduction to a statistically
sound one-bit-round proof. Fix a nondecreasing polynomial `p` and `λ = λ(n)` with `n ≤ p(λ(n))`. Let
`L = L_R` have a polynomial-time two-message argument `Π = (V₁, V₂, P)` with soundness baseline
`c₀`, verifier-message length `ℓ_V(λ, n)` and prover-message length `ℓ_P(λ, n)` (over witnesses of
length `≤ q(n)`). Let its non-adaptive soundness admit a non-uniform, one-query, `T(λ, n)`-time
black-box reduction `(R, F)` with advice of description complexity `s_F(λ, n)` to the Γ-hardness of
`(C, c)` at its target-parameter map, `λ ≤ Γ ≤ T`. Assume the completeness error `κ` of `Π`
satisfies `κ(λ, n) ≤ Γ(λ, n)^{−K}` for every `K > 0`, all large `λ` and all `n ≤ p(λ)`, and that
`(C, c)` is secure against `R ∘ P` at `f`. For each `x ∉ L` fix a description `D_{λ,x}` of the
advice sampler of length `≤ s_F(λ, n)`, and let
`L^F_yes = {(1^λ, x, D) : x ∈ L, |D| ≤ s_F(λ, n)}`, `L^F_no = {(1^λ, x, D_{λ,x}) : x ∉ L}`,
`λ = λ(|x|)`. Then there are error bounds `ϵ_c, ϵ_s` with `1 − ϵ_c(n) − ϵ_s(n) ≥ 1/poly(Γ(λ, n))` such
that `(L^F_yes, L^F_no) ∈ IP(rounds = 1, verifier time = poly(T(λ, n), s_F(λ, n)), prover comm =
ℓ_P(λ, n), verifier comm = ℓ_V(λ, n), completeness ≥ 1 − ϵ_c, soundness ≤ ϵ_s)`; the verifier is
uniform and reads `D` as part of its input.

**Formalization Note** The common input is the pair `(x, D)`, encoded as `(1^{λ(|x|)}, x, D)`.
Verifier randomness is the default `O(verifier time)`. The standing assumptions (§4.1.1, p.15) are
hypotheses: `λ(·), T, Γ, s_F, ℓ_P, ℓ_V` time-constructible, `c, c₀` efficiently computable; and the
error bounds produced are efficiently computable. -/
theorem theorem_6_3 (p : Polynomial ℕ) (hp : Monotone p.eval) (lamF : ℕ → ℕ)
    (hlam : ∀ n, n ≤ p.eval (lamF n))
    (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ) (hRel : IsNPRel Rel q)
    (A : LaconicArg) (hA : A.IsPPT) (c₀ : ℝ) (h0 : 0 ≤ c₀) (h1 : c₀ < 1) (ℓV ℓP : ℕ → ℕ → ℕ)
    (hℓV : ∀ (lam : ℕ) (x : List Bool) (ρ : Fin (A.vcoins lam x) → Bool),
      (A.V1 lam x ρ).1.length ≤ ℓV lam x.length)
    (hℓP : ∀ (lam : ℕ) (x w : List Bool) (ρ : Fin (A.vcoins lam x) → Bool)
      (ρ' : Fin (A.pcoins (A.V1 lam x ρ).1 x w) → Bool), w.length ≤ q.eval x.length →
      (A.P (A.V1 lam x ρ).1 x w ρ').length ≤ ℓP lam x.length)
    (R : Reduction) (F : ℕ → List Bool → PMF (List Bool)) (G : Game) (T Γ sF : ℕ → ℕ → ℕ)
    (hT : ∀ lam n, lam + n ≤ T lam n) (hTime : R.IsTTime G T)
    (hAdv : AdviceBounded F (Lang Rel)ᶜ T) (hOne : R.IsKQuery (fun _ _ => 1))
    (hDesc : HasDescription F (Lang Rel)ᶜ sF) (hΓ : ∀ lam n, lam ≤ Γ lam n ∧ Γ lam n ≤ T lam n)
    (hRed : IsBBReduction (A.source c₀ h0 h1) (Lang Rel)ᶜ R F G Γ)
    (hκ : ∀ K : ℕ, 0 < K → ∀ᶠ lam : ℕ in Filter.atTop, ∀ x w : List Bool,
      x.length ≤ p.eval lam → w.length ≤ q.eval x.length → Rel x w →
      1 - (((Γ lam x.length : ℕ) : ℝ) ^ K)⁻¹ ≤ A.honestAcc lam x w)
    (hlamc : TimeConstr (fun n => [unary n]) lamF)
    (hTc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => T a.1 a.2))
    (hΓc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => Γ a.1 a.2))
    (hsc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => sF a.1 a.2))
    (hℓPc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => ℓP a.1 a.2))
    (hℓVc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => ℓV a.1 a.2))
    (hcc : EffReal G.c) (hc0c : EffReal c₀)
    (dummy : List Bool) (hSec : SecureHonest G A Rel q.eval R (fun _ _ => 1) T dummy p.eval T)
    (Dsel : List Bool → List Bool)
    (hD : ∀ x ∉ Lang Rel, (Dsel x).length ≤ sF (lamF x.length) x.length ∧
      IsSamplerCode (Dsel x) (F (lamF x.length) x)) :
    ∃ (εc εs : ℕ → ℝ) (e d C : ℕ),
      (∀ n, εc n ∈ Set.Icc (0 : ℝ) 1 ∧ εs n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, ((((Γ (lamF n) n : ℕ) : ℝ) + 2) ^ e)⁻¹ ≤ 1 - εc n - εs n) ∧
      EffComputable (fun n => [unary n]) εc (fun n => (T (lamF n) n + sF (lamF n) n + 2) ^ d) ∧
      EffComputable (fun n => [unary n]) εs (fun n => (T (lamF n) n + sF (lamF n) n + 2) ^ d) ∧
      InIP (I := List Bool × List Bool) (fun i => [unary (lamF i.1.length), i.1, i.2])
        {i | i.1 ∈ Lang Rel ∧ i.2.length ≤ sF (lamF i.1.length) i.1.length}
        {i | i.1 ∉ Lang Rel ∧ i.2 = Dsel i.1} 1
        (fun i => (T (lamF i.1.length) i.1.length + sF (lamF i.1.length) i.1.length + 2) ^ d)
        (fun i => ℓP (lamF i.1.length) i.1.length) (fun i => ℓV (lamF i.1.length) i.1.length)
        (fun i => C * ((T (lamF i.1.length) i.1.length + sF (lamF i.1.length) i.1.length + 2) ^ d
          + 1))
        (fun i => εc i.1.length) (fun i => εs i.1.length) := by sorry

end LaconicBarrier
