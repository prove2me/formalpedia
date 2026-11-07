-- Prove2me | Theorems.Thm_LaconicBarrier_corollary_7_3_composition
-- name    : LaconicBarrier.corollary_7_3_composition
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:02.997882+00:00
-- url     : https://prove2.me/theorems/046c992d-45af-458d-9794-c804ba2b2fd9
-- title:
--   Proof of Corollary 7.3 — witness encryption from iO with a one-query reduction
-- statement:
--   Let $i\mathcal O$ be a correct polynomial-time obfuscator, $\mathcal R$ an NP relation with witness bound $q$, and $(\mathcal R, F)$ a one-query, $T$-time black-box reduction from iO security to the $T$-hardness of $(\mathcal C, c)$ at $f$, with $T(\lambda, n) \ge \lambda + n$ polynomial and advice of polynomial description complexity, and suppose $(\mathcal C, c)$ is $T$-hard at $f$ for every polynomial index bound. Then:
--
--   1. there is a witness encryption scheme $(\mathrm{Enc}, \mathrm{Dec})$ for $\mathcal R$ that encrypts $b$ under $x$ as $i\mathcal O(1^\lambda, C_{x,b})$ (with the obfuscator's coins), where $C_{x,b}$ has $m(|x|)$ inputs and is padded to $g(|x|)$ gates, $m, g$ polynomial, and $C_{x,b}(w) = b \wedge [(x, w) \in \mathcal R]$ on every padded witness $w$ with $|w| \le q(|x|)$;
--   2. there are a polynomial $s$ and the index map $x \mapsto (C_{x,0}, C_{x,1})$ (the code of that pair) of length $s(|x|)$, whose value is an admissible pair for every $x \notin L$;
--   3. there is a one-query, $T'$-time reduction $(\mathcal R', F')$ for the witness-encryption game on the false statements, with $T'(\lambda,n) \ge \lambda + n$ polynomial, advice $F'(1^\lambda, x) = F(1^\lambda, (C_{x,0}, C_{x,1}))$ bounded by $T'$ and of polynomial description complexity, target-parameter map $f'(1^\lambda, n) = f(1^\lambda, s(n))$, which is a reduction to the $T'$-hardness of $(\mathcal C, c)$;
--   4. $(\mathcal C, c)$ is $T'$-hard at $f'$ for index lengths $n \le \lambda$.
--
--   With Corollary 7.1 this gives $L \in \mathsf{coAM}$ for every NP language, i.e. Corollary 7.3.
--
--   Differences from the source:
--   - reading: 'can be constructed' (encrypt b as iO(1^λ, C_{x,b}), C_{x,b} padded to size s(n)); 'polynomial overhead; it is still a reduction to the T-hardness of (C, c)' → Enc(1^λ, x, b) = iO(1^λ, C_{x,b}) for circuits C_{x,b} of polynomial input length m and padded gate count g with C_{x,b}(w) = b ∧ R(x, w) on padded witnesses, the index map x ↦ code of (C_{x,0}, C_{x,1}) of length s(|x|); existence of the composed reduction and T′ with the listed properties, including T′-hardness at f′ for n ≤ λ; reason: the construction is the paper's; the composed reduction is described on the page only by its advice, target map, query count and overhead, which are the properties stated
--   - reading: (C, c) T-hard at f (Definition 4.12), the index bound p not named → T-hard at f for every polynomial p; reason: the padded index has length s(n) with s depending on L, so 'every L ∈ NP' needs every p
--   - generalization: iO for circuits (any number of outputs) → an obfuscator for the published single-output circuits (KarpLiptonOM.Circuit); reason: an obfuscator for all circuits, with its reduction, restricts to single-output circuits; the proof of Corollary 7.3 uses C_{x,b}(w) = b ∧ R(x, w)
--   - generalization: an indistinguishability obfuscator (correctness and security, Definition 4.11) → correctness and polynomial time only (IOScheme.IsIO); security not assumed; reason: the proof never uses it; a secure obfuscator satisfies the weaker hypothesis
--   - reading: witness encryption for R with message length ℓ(λ) (Definition 4.8) → one-bit messages; Dec outputs [µ] or any other string (⊥); security is the fixed-message game with the pair (0, 1); reason: §7.1 uses WE 'supporting one-bit messages', and the query count refers to the ciphertext-to-bit oracle (p.18)
--   - generalization: a witness encryption scheme (correctness and security, Definition 4.8) → correctness and polynomial time only (WEScheme.IsWE); security not assumed; reason: the proof never uses it; a secure scheme satisfies the weaker hypothesis
--   - encoding: T(λ, n) = poly(λ, n), T(λ, n) ≥ λ + n; a reduction running in polynomial time → λ + n ≤ T(λ, n) ≤ (λ + n + 2)^c; the reduction is T-time for the same T; reason: for polynomials T, T_R ≥ λ + n the maximum serves both: T-hardness and max(T, T_R)-hardness coincide, and a reduction to T-hardness is one to max-hardness
--   - encoding: advice of description complexity s_F (a Boolean-circuit description of r ↦ F(1^λ, x; r)); uniform or non-uniform → a circuit code (MCircuit.code) of length ≤ s_F whose output on uniform input bits, read by unpadOut, has distribution exactly F(1^λ, x); a uniform reduction is the one-gate sampler of the empty string; reason: a fixed, injective, polynomial-time decodable circuit encoding; the uniform case is a special case
--   - generalization: T-time reduction: one target-game execution, including f and the challenger at λ′, takes at most T(λ,|x|) steps → each step of the reduction, the challenger at λ′ = f(1^λ, n) and f computable within (T+2)^c steps, with at most (T+2)^c coins and actions, for one constant c; reason: every strict T-time reduction satisfies this; the paper's arguments use only that the execution is simulable in poly(T) (p.21)
--   - encoding: at most k oracle calls in one target-game execution → no query on any view (reachable or not) that already holds k replies; reason: a reduction can be modified on unreachable views without changing any execution
--   - encoding: a polynomial p with δ(λ) > 1/p(Γ(λ)) infinitely often → δ(λ) > (Γ(λ)+2)^(−e) for some e ∈ ℕ, infinitely often; reason: every positive polynomial is at most (t+2)^e; avoids 1/p = 1/0 = 0
--   - encoding: possibly unbounded randomized source adversary, fresh coins on each call → a distribution on strings for each query (PMF), sampled independently on each call; reason: the paper's stateless oracle model, fully general
--   - encoding: probabilistic challenger with any number of rounds → coins and number of actions bounded at each λ; the challenger speaks first; running out of actions is lose; reason: at the target parameters the T-time bound bounds both; elsewhere the game is never run
--   - encoding: NP relation: polynomial-time decidable, witness bound q → IsNPRel: the published PolyPred2 (one-tape CookPvsNP machines on x#w) and |w| ≤ q(|x|) for a polynomial q; reason: same class of relations and languages
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), proof of Corollary 7.3, pp.46–47 (PDF pp.49–50)

import Mathlib
import Definitions.Def_LaconicBarrier_Lang
import Definitions.Def_LaconicBarrier_IOScheme_source
import Definitions.Def_LaconicBarrier_WEScheme_source
import Definitions.Def_LaconicBarrier_IsBBReduction
import Definitions.Def_LaconicBarrier_Reduction_IsTTime
import Definitions.Def_LaconicBarrier_Reduction_IsKQuery
import Definitions.Def_LaconicBarrier_AdviceBounded
import Definitions.Def_LaconicBarrier_HasDescription
import Definitions.Def_LaconicBarrier_THardAt

namespace LaconicBarrier

open Classical in
/-- **Witness encryption from iO with a one-query reduction** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), proof of Corollary 7.3,
pp.46–47): to encrypt a bit `b` under `x`, output `iO(1^λ, C_{x,b})` for the padded circuit
`C_{x,b}` of size `s(n) = poly(n)`; for `x ∉ L` the circuits `C_{x,0}`, `C_{x,1}` are functionally
equivalent. Composing with a one-query, `T`-time reduction `(R, F)` for iO to the `T`-hardness of
`(C, c)` gives a one-query reduction for witness encryption, with advice
`F(1^λ, (C_{x,0}, C_{x,1}))`, target-parameter map `(1^λ, n) ↦ f(1^λ, s(n))` and polynomial
overhead, still a reduction to the hardness of `(C, c)`. Precisely: given an obfuscator, an NP
relation `R`, a polynomial `T(λ, n) ≥ λ + n` and such a reduction with advice of polynomial
description complexity, with `(C, c)` `T`-hard at `f` for every polynomial index bound, there are

1. a witness encryption scheme `(Enc, Dec)` for `R` (correct and polynomial-time) whose encryption of
   `b` under `x` is `iO(1^λ, C_{x,b})`, for circuits `C_{x,b}` with `m(|x|)` inputs and padded to
   `g(|x|)` gates (`m`, `g` polynomial) with `C_{x,b}(w) = b ∧ [(x, w) ∈ R]` on every padded witness
   `w` of length at most `q(|x|)`;
2. a polynomial `s` and the index map `x ↦ (C_{x,0}, C_{x,1})` (the code of that pair) of length
   `s(|x|)`, admissible for every `x ∉ L`;
3. a one-query, `T′`-time reduction `(R′, F′)` for the witness-encryption game on `X = {x ∉ L}`, with
   `T′(λ, n) ≥ λ + n` polynomial, `F′(1^λ, x) = F(1^λ, (C_{x,0}, C_{x,1}))`, `f′(1^λ, n) = f(1^λ, s(n))`,
   advice bounded by `T′` and of polynomial description complexity, which is a reduction to the
   `T′`-hardness of `(C, c)`;
4. and `(C, c)` is `T′`-hard at `f′` for index lengths `n ≤ λ`.

**Formalization Note** The encryption's coins are the obfuscator's coins at `(λ, m(|x|), g(|x|))`
(`hco`, read through `Fin.cast`). Circuits are single-output: `C_{x,b}(w) = b ∧ R(x, w)` on padded witnesses
(`⊥` read as `0`), so for `x ∉ L` both circuits are identically `0`. -/
theorem corollary_7_3_composition (O : IOScheme) (hO : O.IsIO)
    (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ) (hRel : IsNPRel Rel q)
    (R : Reduction) (F : ℕ → List Bool → PMF (List Bool)) (G : Game) (T : ℕ → ℕ → ℕ)
    (hTpoly : ∃ c : ℕ, ∀ lam n, T lam n ≤ (lam + n + 2) ^ c) (hT : ∀ lam n, lam + n ≤ T lam n)
    (hTime : R.IsTTime G T) (hAdv : AdviceBounded F IOScheme.admissible T)
    (hOne : R.IsKQuery (fun _ _ => 1))
    (hDesc : ∃ (sF : ℕ → ℕ → ℕ) (d : ℕ), (∀ lam n, sF lam n ≤ (lam + n + 2) ^ d) ∧
      HasDescription F IOScheme.admissible sF)
    (hRed : IsBBReduction O.source IOScheme.admissible R F G T)
    (hHard : ∀ p : Polynomial ℕ, THardAt G T R.f p.eval) :
    ∃ (E : WEScheme) (m g : ℕ → ℕ) (Cx : (x : List Bool) → Bool → KarpLiptonOM.Circuit (m x.length))
      (hco : ∀ lam x, E.ecoins lam x = O.coins lam (m x.length) (g x.length)),
      E.IsWE Rel ∧
      (∃ c : ℕ, ∀ n, m n ≤ (n + 2) ^ c ∧ g n ≤ (n + 2) ^ c) ∧
      (∀ x b, (Cx x b).gates.length = g x.length) ∧
      (∀ x w b, w.length ≤ q.eval x.length →
        (Cx x b).eval (padIn (m x.length) w) = (b && decide (Rel x w))) ∧
      (∀ lam x b (ρ : Fin (E.ecoins lam x) → Bool), E.Enc lam x b ρ =
        circCode (O.obf lam (m x.length) (g x.length) (Cx x b)
          (fun i => ρ (Fin.cast (hco lam x).symm i)))) ∧
    ∃ (s : ℕ → ℕ) (idx : List Bool → List Bool),
      (∃ c : ℕ, ∀ n, s n ≤ (n + 2) ^ c) ∧ (∀ x, idx x = pairCode (Cx x false) (Cx x true)) ∧
      (∀ x, (idx x).length = s x.length) ∧
      (∀ x ∉ Lang Rel, idx x ∈ IOScheme.admissible) ∧
    ∃ (R' : Reduction) (F' : ℕ → List Bool → PMF (List Bool)) (T' : ℕ → ℕ → ℕ),
      (∃ c : ℕ, ∀ lam n, T' lam n ≤ (lam + n + 2) ^ c) ∧ (∀ lam n, lam + n ≤ T' lam n) ∧
      (∀ lam x, F' lam x = F lam (idx x)) ∧ (∀ lam n, R'.f lam n = R.f lam (s n)) ∧
      R'.IsTTime G T' ∧ AdviceBounded F' (Lang Rel)ᶜ T' ∧ R'.IsKQuery (fun _ _ => 1) ∧
      (∃ (sF : ℕ → ℕ → ℕ) (d : ℕ), (∀ lam n, sF lam n ≤ (lam + n + 2) ^ d) ∧
        HasDescription F' (Lang Rel)ᶜ sF) ∧
      IsBBReduction E.source (Lang Rel)ᶜ R' F' G T' ∧
      THardAt G T' R'.f (fun lam => lam) := by sorry

end LaconicBarrier
