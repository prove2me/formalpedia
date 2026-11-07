-- Prove2me | Theorems.Thm_LaconicBarrier_corollary_6_4
-- name    : LaconicBarrier.corollary_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:30.774206+00:00
-- url     : https://prove2.me/theorems/a9dfe95a-96dc-4d13-b5dd-5c5699bb4587
-- title:
--   Corollary 6.4 — $L \in \mathsf{coAM}$ with verifier time $2^{\ell_P}\,\mathrm{poly}(T, s_F)$
-- statement:
--   Under the hypotheses of Theorem 6.3, with $\lambda = \lambda(n)$ and $n = |x|$,
--   $$
--   L \in \mathsf{coAM}\bigl(\text{rounds} = 1,\ \text{verifier time} = 2^{\ell_P(\lambda,n)} \cdot \mathrm{poly}(T(\lambda,n), s_F(\lambda,n)),\ \text{prover comm, verifier comm, verifier randomness} = \mathrm{poly}(T(\lambda,n), s_F(\lambda,n))\bigr),
--   $$
--   with completeness at least $2/3$ and soundness at most $1/3$.
--
--   For a one-bit argument ($\ell_P = 1$) with polynomial $T$ and $s_F$ this is $L \in \mathsf{coAM}$ with polynomial resources, which is how Corollaries 7.1 and 7.3 conclude.
--
--   Differences from the source:
--   - generalization: a two-message laconic argument (Definition 4.6: negligible completeness for every p, succinctness, soundness) → polynomial-time algorithms (V₁, P, V₂) with message bounds ℓ_V, ℓ_P and only the stated completeness hypothesis; reason: the proof uses neither soundness nor succinctness (only through ℓ_P); the printed hypotheses imply these
--   - encoding: every real constant K > 0 → every K ∈ ℕ, K > 0; reason: Γ ≥ λ ≥ 1 for large λ, so the bound for ⌈K⌉ implies the one for K
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
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Corollary 6.4, p.41 (PDF p.44)

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

/-- **Corollary 6.4** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Corollary 6.4, p.41): under the hypotheses of Theorem 6.3,
`L ∈ coAM(rounds = 1, verifier time = 2^{ℓ_P(λ,n)} · poly(T(λ, n), s_F(λ, n)), prover comm, verifier
comm, verifier randomness = poly(T(λ, n), s_F(λ, n)))`, with `λ = λ(n)`, `n = |x|`, completeness at
least `2/3` and soundness at most `1/3`.

**Formalization Note** `coAM(…)` of `L` is `AM(…)` for `(L̄, L)` on inputs `x`. The hypotheses are
those of `theorem_6_3` without the choice of the descriptions `D_{λ,x}` (which exist by the
description-complexity hypothesis). -/
theorem corollary_6_4 (p : Polynomial ℕ) (hp : Monotone p.eval) (lamF : ℕ → ℕ)
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
    (dummy : List Bool) (hSec : SecureHonest G A Rel q.eval R (fun _ _ => 1) T dummy p.eval T) :
    ∃ d : ℕ, InAM (I := List Bool) (fun x => [x]) (Lang Rel)ᶜ (Lang Rel) 1
      (fun x => 2 ^ ℓP (lamF x.length) x.length *
        (T (lamF x.length) x.length + sF (lamF x.length) x.length + 2) ^ d)
      (fun x => (T (lamF x.length) x.length + sF (lamF x.length) x.length + 2) ^ d)
      (fun x => (T (lamF x.length) x.length + sF (lamF x.length) x.length + 2) ^ d)
      (fun x => (T (lamF x.length) x.length + sF (lamF x.length) x.length + 2) ^ d)
      (fun _ => 1 / 3) (fun _ => 1 / 3) := by sorry

end LaconicBarrier
