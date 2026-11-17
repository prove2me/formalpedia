-- Prove2me | Theorems.Thm_LaconicBarrier_Supplement_theorem_6_8
-- name    : LaconicBarrier.Supplement.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:35:54.553412+00:00
-- url     : https://prove2.me/theorems/1014f82b-c556-45f4-a847-9bf1df9df69e
-- title:
--   Theorem 6.8 — adaptive SNARG with a one-query reduction gives a one-round proof with an instance-independent first message
-- statement:
--   Fix a nondecreasing polynomial $p$ and a security-parameter function $\lambda = \lambda(n)$ with $n \le p(\lambda(n))$ for every $n$. Let $L = L_{\mathcal R}$ for an NP relation $\mathcal R$ with witness bound $q$, and let $\Pi = (G, P, V)$ be an adaptively sound SNARG for $\mathcal R$. Suppose its adaptive soundness admits a non-uniform, one-query, $T(\lambda,n)$-time black-box reduction $(\mathcal R, F)$ to a game-based assumption $(\mathcal C, c)$, with advice $F(1^\lambda, 1^n)$ of description complexity $s_F(\lambda, n)$. Here $\ell_P(\lambda, n) \ge 1$ bounds the proof length and $\ell_V(\lambda, n)$ the proving-key length. Assume:
--
--   1. $(\mathcal C, c)$ is secure against $\mathcal R \circ P$ at the reduction's target-parameter map $f$ (Definition 6.1, adaptive form);
--   2. the standing assumptions: $\lambda(\cdot), T, s_F, \ell_P, \ell_V$ are time-constructible and $c$ is efficiently computable.
--
--   For each $n$ fix a sampler description $D_n$ with $D_n(\rho) = F(1^{\lambda(n)}, 1^n; \rho)$ and $|D_n| \le s_F(\lambda(n), n)$. Then there is a one-round private-coin proof for $L$ whose uniform verifier is given a sampler description $D$ as part of its input, with:
--
--   1. verifier time $\mathrm{poly}(T(\lambda, n), s_F(\lambda, n))$, prover messages of at most $\ell_P(\lambda, n)$ bits and verifier messages of at most $\ell_V(\lambda, n)$ bits;
--   2. efficiently computable error bounds with
--   $$
--   1 - \epsilon_c(n) - \epsilon_s(n) \ge \frac{1}{\mathrm{poly}(\lambda, n)} ;
--   $$
--   3. completeness for every $x \in L$ and every candidate description $D$ with $|D| \le s_F(\lambda, n)$, and statistical soundness on every $x \notin L$ of length $n$ with $D = D_n$;
--   4. a first verifier message that depends on $x$ only through its length: $V'_1(1^\lambda, x, D; \rho) = V'_1(1^\lambda, 1^n, D; \rho)$ for every allowed $D$ and every random tape $\rho$.
--
--   Here $\lambda = \lambda(n)$ and $n = |x|$.
--
--   Together with Theorem 5.2 this gives circuits of size $2^{\ell_P}\mathrm{poly}(T, s_F)$ for $L$ (Corollary 6.9).
--
--   **Formalization Note** The common input is the pair $(x, D)$, encoded as $(1^{\lambda(|x|)}, x, D)$, as in the published Theorem 6.3. Verifier randomness is the default $O(\text{verifier time})$. The sampler descriptions are circuit codes (Definition 4.15). The first-message clause includes equality of the coin counts.
--
--   Differences from the source:
--   - generalization: adaptively sound SNARG (Definition 4.7: completeness, succinctness, adaptive soundness) → polynomial-time (G, P, V) with the completeness of Definition 4.7 and the explicit length bounds; adaptive soundness and succinctness are not hypotheses; reason: the proof uses neither (succinctness only through ℓ_P, soundness only through the reduction guarantee); every adaptively sound SNARG satisfies the Lean hypotheses
--   - encoding: negligible completeness error κ(λ) for every polynomial p → for every K > 0, for all large λ, acceptance ≥ 1 − λ^(−K) on every (x, w) ∈ R with |x| ≤ p(λ), |w| ≤ q(|x|); reason: equivalent: finitely many pairs per λ
--   - encoding: adaptive-soundness game C_{1^n}: receive (x, π) → SNARG.adaptiveSource: the response is the tuple code tup [x, π], other strings lose; index set {1^n}; reason: one-string replies in the published two-message game family; tup is injective
--   - reading: black-box reduction to a game-based assumption (C, c) → IsBBReduction with Γ(λ, n) = λ (Definition 4.13); reason: p.37: 'For a reduction to (C, c) (Definition 4.13), we apply the lemma with Γ(λ, n) = λ'
--   - reading: ℓ_P(λ, n) bounds the proof length → every honest proof P(pk, x, w) with pk from G(1^λ, 1^{|x|}) and |w| ≤ q(|x|) has length ≤ ℓ_P(λ, |x|); reason: §6, p.37: 'ℓ_P(λ, n) bounds the prover-message length over all witnesses of length at most q(n)'
--   - encoding: (C, c) is secure against R ∘ P at f (Definition 6.1), adaptive form → SecureHonestAd with k = 1 and Γ = T; reason: Definition 6.1: 'secure against R ∘ P at f if it is T-secure against this algorithm'
--   - generalization: T-time reduction: one target-game execution, including f and the challenger at λ′, takes at most T(λ,|x|) steps → the published Reduction.IsTTime: each step of the reduction, the challenger at λ′ and f computable within (T+2)^c steps, with at most (T+2)^c coins and actions; reason: every strict T-time reduction satisfies it; the paper's arguments use only that the execution is simulable in poly(T) (p.21)
--   - encoding: advice of description complexity s_F(λ, n), D_n(ρ) = F(1^{λ(n)}, 1^n; ρ), |D_n| ≤ s_F → HasDescription F {1^n} s_F, and a fixed choice n ↦ D_n of circuit codes (IsSamplerCode) of length ≤ s_F(λ(n), n); the statement holds for every such choice; reason: Definition 4.15; 'fix' is a universally quantified choice
--   - encoding: one-round private-coin proof for L with a uniform verifier given a sampler description D_n → IPVerifier.Proves for the promise problem on pairs (x, D) encoded (1^{λ(|x|)}, x, D): yes = {x ∈ L, |D| ≤ s_F}, no = {x ∉ L, D = D_{|x|}}; verifier randomness C·(time + 1); reason: completeness 'for every candidate sampler description D' and soundness 'for the same description D_n', as the page states; default randomness (p.25)
--   - encoding: 1 − ϵ_c(n) − ϵ_s(n) ≥ 1/poly(λ, n) → ≥ (λ(n) + n + 2)^(−e) for one e and all n; reason: every positive polynomial in (λ, n) is at most (λ + n + 2)^e
--   - encoding: V′_1(1^λ, x, D; ρ) = V′_1(1^λ, 1^n, D; ρ) for every allowed D and random tape ρ → for every (x, D) with |D| ≤ s_F: V.coins (x, D) = V.coins (1^{|x|}, D) and msg (x, D) ρ [] = msg (1^{|x|}, D) ρ [] with ρ transported; reason: the same random tape requires the same number of coins
--   - reading: there exist completeness and soundness error bounds (standing assumption: error bounds efficiently computable) → the error bounds produced lie in [0, 1] and are efficiently computable; reason: the standing assumption applies to the error bounds the theorem produces, as in the published theorem_6_3
--   - reading: standing assumptions (p.15): resource bounds time-constructible, baselines and error bounds efficiently computable, 'we do not repeat these conditions' → explicit hypotheses TimeConstr / EffComputable / EffReal on the bounds and constants the statement uses; reason: the paper's own convention, applied as in the published theorem_6_3
--   - encoding: at most k oracle calls in one target-game execution → the published Reduction.IsKQuery: no query on any view (reachable or not) holding k replies; reason: a reduction can be modified on unreachable views without changing any execution
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 6.8, p.43 (PDF 46); Definition 6.1, p.37; Definition 4.7, pp.17–18

import Mathlib
import Definitions.Def_LaconicBarrier_Lang
import Definitions.Def_LaconicBarrier_Supplement_SNARG
import Definitions.Def_LaconicBarrier_Supplement_SecureHonestAd
import Definitions.Def_LaconicBarrier_IsBBReduction
import Definitions.Def_LaconicBarrier_Reduction_IsTTime
import Definitions.Def_LaconicBarrier_Reduction_IsKQuery
import Definitions.Def_LaconicBarrier_AdviceBounded
import Definitions.Def_LaconicBarrier_HasDescription
import Definitions.Def_LaconicBarrier_TimeConstr
import Definitions.Def_LaconicBarrier_EffComputable
import Definitions.Def_LaconicBarrier_InIP

namespace LaconicBarrier.Supplement

/-- **Theorem 6.8** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for
Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 6.8, p.43):
adaptive soundness with a one-query reduction gives a one-round proof whose first message does not
depend on the instance. Fix a nondecreasing polynomial `p` and `λ = λ(n)` with `n ≤ p(λ(n))`. Let
`L = L_R` have an adaptively sound SNARG `Π = (G, P, V)` whose soundness admits a non-uniform,
one-query, `T(λ, n)`-time black-box reduction `(R, F)` to `(C, c)`, with advice `F(1^λ, 1ⁿ)` of
description complexity `s_F(λ, n)`; `ℓ_P(λ, n) ≥ 1` and `ℓ_V(λ, n)` bound the proof and proving-key
lengths. Assume `(C, c)` is secure against `R ∘ P` at `f` (Definition 6.1, adaptive form). For each
`n` fix a description `D_n` of the sampler `ρ ↦ F(1^{λ(n)}, 1ⁿ; ρ)` with `|D_n| ≤ s_F(λ(n), n)`.
Then there is a one-round private-coin proof with a uniform verifier on common input `(x, D)`: verifier
time `poly(T(λ, n), s_F(λ, n))`, prover and verifier messages of at most `ℓ_P(λ, n)` and `ℓ_V(λ, n)`
bits, errors with `1 − ϵ_c(n) − ϵ_s(n) ≥ 1/poly(λ, n)`; completeness for every `x ∈ L` and every
candidate description `D` with `|D| ≤ s_F(λ, n)`, statistical soundness for every `x ∉ L` of length
`n` with `D = D_n`; and for every allowed `D` and tape `ρ`, `V′₁(1^λ, x, D; ρ) = V′₁(1^λ, 1ⁿ, D; ρ)`.

**Formalization Note** The common input is the pair `(x, D)`, encoded as `(1^{λ(|x|)}, x, D)`, as in
the published `theorem_6_3`. "A reduction to `(C, c)`" is Definition 4.13 with `Γ(λ, n) = λ`, from
the adaptive-soundness game (index set `{1ⁿ}`), so the advice is `F(1^λ, 1ⁿ)`. "Adaptively sound
SNARG" enters through polynomial time, completeness and the length bounds; the soundness property
and succinctness are not hypotheses (see the differences list). Verifier randomness is the default
`O(verifier time)`. The standing assumptions (§4.1.1, p.15) are hypotheses: `λ(·), T, s_F, ℓ_P, ℓ_V`
time-constructible and `c` efficiently computable (the SNARG's baseline is `0`); the error bounds
produced are efficiently computable. "The first message depends on `x` only through its length"
includes the number of coins, transported along the stated equality. -/
theorem theorem_6_8 (p : Polynomial ℕ) (hp : Monotone p.eval) (lamF : ℕ → ℕ)
    (hlam : ∀ n, n ≤ p.eval (lamF n))
    (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ) (hRel : IsNPRel Rel q)
    (S : SNARG) (hS : S.IsPPT) (hSc : S.Complete Rel q) (ℓV ℓP : ℕ → ℕ → ℕ)
    (hℓP1 : ∀ lam n, 1 ≤ ℓP lam n)
    (hℓV : ∀ (lam n : ℕ) (ρ : Fin (S.gcoins lam n) → Bool), (S.G lam n ρ).1.length ≤ ℓV lam n)
    (hℓP : ∀ (lam : ℕ) (x w : List Bool) (ρ : Fin (S.gcoins lam x.length) → Bool)
      (ρ' : Fin (S.pcoins (S.G lam x.length ρ).1 x w) → Bool), w.length ≤ q.eval x.length →
      (S.P (S.G lam x.length ρ).1 x w ρ').length ≤ ℓP lam x.length)
    (R : Reduction) (F : ℕ → List Bool → PMF (List Bool)) (G : Game) (T sF : ℕ → ℕ → ℕ)
    (hT : ∀ lam n, lam + n ≤ T lam n) (hTime : R.IsTTime G T)
    (hAdv : AdviceBounded F unaryIdx T) (hOne : R.IsKQuery (fun _ _ => 1))
    (hDesc : HasDescription F unaryIdx sF)
    (hRed : IsBBReduction (S.adaptiveSource Rel) unaryIdx R F G (fun lam _ => lam))
    (hlamc : TimeConstr (fun n => [unary n]) lamF)
    (hTc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => T a.1 a.2))
    (hsc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => sF a.1 a.2))
    (hℓPc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => ℓP a.1 a.2))
    (hℓVc : TimeConstr (ι := ℕ × ℕ) (fun a => [unary a.1, unary a.2]) (fun a => ℓV a.1 a.2))
    (hcc : EffReal G.c)
    (dummy : List Bool)
    (hSec : SecureHonestAd G S Rel q.eval R (fun _ _ => 1) T dummy p.eval T)
    (Dsel : ℕ → List Bool)
    (hD : ∀ n, (Dsel n).length ≤ sF (lamF n) n ∧ IsSamplerCode (Dsel n) (F (lamF n) (unary n))) :
    ∃ (εc εs : ℕ → ℝ) (e d C : ℕ),
      (∀ n, εc n ∈ Set.Icc (0 : ℝ) 1 ∧ εs n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, ((((lamF n + n : ℕ) : ℝ) + 2) ^ e)⁻¹ ≤ 1 - εc n - εs n) ∧
      EffComputable (fun n => [unary n]) εc (fun n => (T (lamF n) n + sF (lamF n) n + 2) ^ d) ∧
      EffComputable (fun n => [unary n]) εs (fun n => (T (lamF n) n + sF (lamF n) n + 2) ^ d) ∧
      ∃ V : IPVerifier (List Bool × List Bool),
        V.Proves (fun i => [unary (lamF i.1.length), i.1, i.2])
          {i | i.1 ∈ Lang Rel ∧ i.2.length ≤ sF (lamF i.1.length) i.1.length}
          {i | i.1 ∉ Lang Rel ∧ i.2 = Dsel i.1.length} 1
          (fun i => (T (lamF i.1.length) i.1.length + sF (lamF i.1.length) i.1.length + 2) ^ d)
          (fun i => ℓP (lamF i.1.length) i.1.length) (fun i => ℓV (lamF i.1.length) i.1.length)
          (fun i => C * ((T (lamF i.1.length) i.1.length + sF (lamF i.1.length) i.1.length + 2) ^ d
            + 1))
          (fun i => εc i.1.length) (fun i => εs i.1.length) ∧
        ∀ i : List Bool × List Bool, i.2.length ≤ sF (lamF i.1.length) i.1.length →
          ∃ hc : V.coins i = V.coins (unary i.1.length, i.2),
            ∀ ρ : Fin (V.coins i) → Bool,
              V.msg i ρ [] = V.msg (unary i.1.length, i.2) (fun t => ρ (Fin.cast hc.symm t)) [] := by sorry

end LaconicBarrier.Supplement
