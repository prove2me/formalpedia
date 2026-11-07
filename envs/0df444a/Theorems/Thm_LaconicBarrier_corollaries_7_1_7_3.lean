-- Prove2me | Theorems.Thm_LaconicBarrier_corollaries_7_1_7_3
-- name    : LaconicBarrier.corollaries_7_1_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:47:38.257164+00:00
-- url     : https://prove2.me/theorems/30b62432-57fb-4706-8cb9-05a64bc6eb29
-- title:
--   Corollaries 7.1 and 7.3 — a one-query black-box reduction of WE or iO to a falsifiable assumption gives $\mathsf{NP} \subseteq \mathsf{coAM}$ and collapses $\mathsf{PH}$
-- statement:
--   This is the paper's first headline result: *if iO for circuits or WE for NP admits a one-query, non-uniform black-box reduction to a falsifiable assumption, then $\mathsf{NP} \subseteq \mathsf{coAM}$, and the polynomial hierarchy collapses.* It has three parts.
--
--   1. **Corollary 7.1 (witness encryption).** Let $L = L_{\mathcal R}$ for an NP relation $\mathcal R$. Suppose a witness encryption scheme for $\mathcal R$ admits a one-query black-box security reduction $(\mathcal R, F)$, running in time $T(\lambda, n) = \mathrm{poly}(\lambda, n)$ with $T \ge \lambda + n$, uniform or with advice of description complexity $\mathrm{poly}(\lambda, n)$, to the $T$-hardness of a game-based assumption $(\mathcal C, c)$ at its target-parameter map $f$, and that $(\mathcal C, c)$ is $T$-hard at $f$. Then
--   $$
--   L \in \mathsf{coAM}\bigl(\text{rounds} = 1,\ \text{verifier time, prover comm, verifier comm, verifier randomness} = \mathrm{poly}(n)\bigr).
--   $$
--   2. **Corollary 7.3 (iO).** If iO for circuits admits such a reduction (its source index set being the admissible circuit pairs) and $(\mathcal C, c)$ is $T$-hard at $f$, then every NP language satisfies the conclusion of part 1: $\mathsf{NP} \subseteq \mathsf{coAM}$.
--   3. **Collapse** ([BHZ87]). If every NP language satisfies that conclusion, there is a $k$ with $\Sigma_j^{\mathsf P} \subseteq \Sigma_k^{\mathsf P}$ for all $j$.
--
--   The time bound of the reduction includes the target challenger at $\lambda' = f(1^\lambda, n)$, so the assumption is falsifiable. Since $\mathsf{NP} \subseteq \mathsf{coAM}$ is believed false, the result is a barrier: basing WE or iO on a falsifiable assumption needs reductions that make more than one query, or are not black-box.
--
--   Differences from the source:
--   - reading: T-hard at f (Definition 4.12), with the index bound p not named → p(λ) = λ in part 1; every polynomial p in part 2; reason: part 1: the proof of Corollary 7.1 sets λ(n) = n, p(λ) = λ (p.46); part 2: the padded iO index has length s(n) with s depending on L
--   - reading: baseline c of the target game (and c₀) efficiently computable (standing assumption, p.15) → EffReal: approximable within 1/(N+1) in time poly(N); reason: the paper does not fix the notion; this is the standard one and what the mixed verifier needs
--   - encoding: T(λ, n) = poly(λ, n), T(λ, n) ≥ λ + n; a reduction running in polynomial time → λ + n ≤ T(λ, n) ≤ (λ + n + 2)^c; the reduction is T-time for the same T; reason: for polynomials T, T_R ≥ λ + n the maximum serves both: T-hardness and max(T, T_R)-hardness coincide, and a reduction to T-hardness is one to max-hardness
--   - reading: witness encryption for R with message length ℓ(λ) (Definition 4.8) → one-bit messages; Dec outputs [µ] or any other string (⊥); security is the fixed-message game with the pair (0, 1); reason: §7.1 uses WE 'supporting one-bit messages', and the query count refers to the ciphertext-to-bit oracle (p.18)
--   - generalization: a witness encryption scheme (correctness and security, Definition 4.8) → correctness and polynomial time only (WEScheme.IsWE); security not assumed; reason: the proof never uses it; a secure scheme satisfies the weaker hypothesis
--   - generalization: iO for circuits (any number of outputs) → an obfuscator for the published single-output circuits (KarpLiptonOM.Circuit); reason: an obfuscator for all circuits, with its reduction, restricts to single-output circuits; the proof of Corollary 7.3 uses C_{x,b}(w) = b ∧ R(x, w)
--   - generalization: an indistinguishability obfuscator (correctness and security, Definition 4.11) → correctness and polynomial time only (IOScheme.IsIO); security not assumed; reason: the proof never uses it; a secure obfuscator satisfies the weaker hypothesis
--   - encoding: advice of description complexity s_F (a Boolean-circuit description of r ↦ F(1^λ, x; r)); uniform or non-uniform → a circuit code (MCircuit.code) of length ≤ s_F whose output on uniform input bits, read by unpadOut, has distribution exactly F(1^λ, x); a uniform reduction is the one-gate sampler of the empty string; reason: a fixed, injective, polynomial-time decodable circuit encoding; the uniform case is a special case
--   - generalization: T-time reduction: one target-game execution, including f and the challenger at λ′, takes at most T(λ,|x|) steps → each step of the reduction, the challenger at λ′ = f(1^λ, n) and f computable within (T+2)^c steps, with at most (T+2)^c coins and actions, for one constant c; reason: every strict T-time reduction satisfies this; the paper's arguments use only that the execution is simulable in poly(T) (p.21)
--   - encoding: at most k oracle calls in one target-game execution → no query on any view (reachable or not) that already holds k replies; reason: a reduction can be modified on unreachable views without changing any execution
--   - encoding: a polynomial p with δ(λ) > 1/p(Γ(λ)) infinitely often → δ(λ) > (Γ(λ)+2)^(−e) for some e ∈ ℕ, infinitely often; reason: every positive polynomial is at most (t+2)^e; avoids 1/p = 1/0 = 0
--   - encoding: non-uniform (probabilistic) adversary circuits of size |A_λ| ≤ Γ(λ) → deterministic multi-output circuits computing each reply from the padded code of the transcript; size = gates + outputs; reason: fixing the best coins never lowers the winning probability or raises the size; other size measures differ polynomially, which T-hardness (every K) absorbs
--   - encoding: possibly unbounded randomized source adversary, fresh coins on each call → a distribution on strings for each query (PMF), sampled independently on each call; reason: the paper's stateless oracle model, fully general
--   - encoding: probabilistic challenger with any number of rounds → coins and number of actions bounded at each λ; the challenger speaks first; running out of actions is lose; reason: at the target parameters the T-time bound bounds both; elsewhere the game is never run
--   - encoding: a negligible function κ bounding the error for all λ → for every e, for all large λ the error is at most (λ+2)^(−e), uniformly in the other arguments; reason: equivalent: take κ(λ) the worst error at λ
--   - encoding: coAM(rounds = 1, verifier time, comm, randomness = poly(n)), default errors 1/3 → InCoAMPoly: a one-round public-coin proof of the complement with all bounds (|x|+2)^d for one d, completeness ≥ 2/3, soundness ≤ 1/3; reason: one exponent bounds all four polynomials (take the maximum)
--   - reading: 'the polynomial hierarchy collapses' (abstract) → ∃ k, ∀ j, Σ_j^P ⊆ Σ_k^P; reason: the meaning of a collapse; [BHZ87] gives k = 2
--   - encoding: NP relation: polynomial-time decidable, witness bound q → IsNPRel: the published PolyPred2 (one-tape CookPvsNP machines on x#w) and |w| ≤ q(|x|) for a polynomial q; reason: same class of relations and languages
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), abstract, PDF p.1; Corollary 7.1, pp.45–46 (PDF pp.48–49); Corollary 7.3, p.46 (PDF p.49)

import Mathlib
import Definitions.Def_LaconicBarrier_Lang
import Definitions.Def_LaconicBarrier_WEScheme_source
import Definitions.Def_LaconicBarrier_IOScheme_source
import Definitions.Def_LaconicBarrier_IsBBReduction
import Definitions.Def_LaconicBarrier_Reduction_IsTTime
import Definitions.Def_LaconicBarrier_Reduction_IsKQuery
import Definitions.Def_LaconicBarrier_AdviceBounded
import Definitions.Def_LaconicBarrier_HasDescription
import Definitions.Def_LaconicBarrier_THardAt
import Definitions.Def_LaconicBarrier_EffComputable
import Definitions.Def_LaconicBarrier_InCoAMPoly
import Definitions.Def_KarpLiptonOM_SigmaP

namespace LaconicBarrier

/-- **Corollaries 7.1 and 7.3, with the collapse of the polynomial hierarchy** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), abstract,
PDF p.1; Corollary 7.1, pp.45–46; Corollary 7.3, p.46): "If iO for circuits or WE for NP admits a
one-query, non-uniform black-box reduction to a falsifiable assumption, then `NP ⊆ coAM`, and the
polynomial hierarchy collapses."

1. (**Corollary 7.1**, witness encryption.) Let `L = L_R` for an NP relation `R`. Suppose a witness
   encryption scheme for `R` admits a one-query black-box security reduction `(R, F)`, running in
   time `T(λ, n) = poly(λ, n)` (`T ≥ λ + n`), uniform or with advice of description complexity
   `poly(λ, n)`, to the `T`-hardness of a game `(C, c)` at its target-parameter map `f`, and that
   `(C, c)` is `T`-hard at `f` (index lengths `n ≤ λ`). Then
   `L ∈ coAM(rounds = 1, verifier time = poly(n), prover comm = poly(n), verifier comm = poly(n),
   verifier randomness = poly(n))`.
2. (**Corollary 7.3**, iO.) If iO for circuits admits such a reduction (its index set the admissible
   circuit pairs) and `(C, c)` is `T`-hard at `f` for every polynomial index bound, then every NP
   language is in that class: `NP ⊆ coAM`.
3. (**Collapse**, [BHZ87].) If every NP language is in that class, there is a `k` with `Σ_j^P ⊆ Σ_k^P`
   for all `j`.

**Formalization Note** "The reduction runs in polynomial time" is `Reduction.IsTTime` with `T`
polynomial (the challenger at `f(1^λ, n)` included, so the assumption is falsifiable); a uniform
reduction is the case of the empty-output sampler. The baseline `c` is efficiently computable (§4.1.1,
p.15). Witness encryption is for one-bit messages with the fixed-message game; iO is for single-output
circuits. Security of WE or iO is not assumed. -/
theorem corollaries_7_1_7_3 :
    (∀ (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ), IsNPRel Rel q →
      ∀ (E : WEScheme), E.IsWE Rel →
      ∀ (R : Reduction) (F : ℕ → List Bool → PMF (List Bool)) (G : Game) (T : ℕ → ℕ → ℕ),
        (∃ c : ℕ, ∀ lam n, T lam n ≤ (lam + n + 2) ^ c) → (∀ lam n, lam + n ≤ T lam n) →
        R.IsTTime G T → AdviceBounded F (Lang Rel)ᶜ T → R.IsKQuery (fun _ _ => 1) →
        (∃ (sF : ℕ → ℕ → ℕ) (d : ℕ), (∀ lam n, sF lam n ≤ (lam + n + 2) ^ d) ∧
          HasDescription F (Lang Rel)ᶜ sF) →
        IsBBReduction E.source (Lang Rel)ᶜ R F G T → THardAt G T R.f (fun lam => lam) →
        EffReal G.c → InCoAMPoly (Lang Rel)) ∧
    (∀ (O : IOScheme), O.IsIO →
      ∀ (R : Reduction) (F : ℕ → List Bool → PMF (List Bool)) (G : Game) (T : ℕ → ℕ → ℕ),
        (∃ c : ℕ, ∀ lam n, T lam n ≤ (lam + n + 2) ^ c) → (∀ lam n, lam + n ≤ T lam n) →
        R.IsTTime G T → AdviceBounded F IOScheme.admissible T → R.IsKQuery (fun _ _ => 1) →
        (∃ (sF : ℕ → ℕ → ℕ) (d : ℕ), (∀ lam n, sF lam n ≤ (lam + n + 2) ^ d) ∧
          HasDescription F IOScheme.admissible sF) →
        IsBBReduction O.source IOScheme.admissible R F G T →
        (∀ p : Polynomial ℕ, THardAt G T R.f p.eval) → EffReal G.c →
        ∀ (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ), IsNPRel Rel q →
          InCoAMPoly (Lang Rel)) ∧
    ((∀ (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ), IsNPRel Rel q →
        InCoAMPoly (Lang Rel)) →
      ∃ k : ℕ, ∀ j : ℕ, KarpLiptonOM.SigmaP j ⊆ KarpLiptonOM.SigmaP k) := by sorry

end LaconicBarrier
