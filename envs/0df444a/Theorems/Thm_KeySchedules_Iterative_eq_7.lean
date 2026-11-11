-- Prove2me | Theorems.Thm_KeySchedules_Iterative_eq_7
-- name    : KeySchedules.Iterative.eq_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:52:17.684023+00:00
-- url     : https://prove2.me/theorems/751d2420-89bf-4dc6-aa3e-146f5e9752b3
-- title:
--   Proof of Theorem 3.1, Eq. (7) — with the master key appended, the ratio for E∘H is that of E at key H(k′), hence ≥ 1 − g★
-- statement:
--   Let $\mathcal E$ be a keyed construction with key space $K$ satisfying the hypotheses of Lemma 2.1 on $\mathcal T_q\times K$ with the key as auxiliary information (data $\mathcal T_{\mathrm{bad}},g$), and let $H:K'\to K$ be a key schedule. For $\mathcal E\circ H$, append the master key $k'$ to the transcript (an independent uniform dummy master key in the ideal world) and write $p^H_b(\bar\tau,k')$ for the resulting transcript probabilities. Whenever $p^H_0(\bar\tau,k')>0$,
--   $$\frac{p^H_1(\bar\tau,k')}{p^H_0(\bar\tau,k')}=\frac{p_1(\bar\tau,H(k'))}{p_0(\bar\tau,H(k'))}\ \ge\ 1-g^\star(\bar\tau,H(k')).$$
--   This is the step that lets the expectation method be applied to $\mathcal E\circ H$ with an empty bad set and the function $(\bar\tau,k')\mapsto g^\star(\bar\tau,H(k'))$.
--
--   Differences from the source:
--
--   - reading: whenever p^H_0(τ̄, k′) > 0 → for τ̄ with at most q queries to each oracle and p^H_0(τ̄, k′) > 0; reason: in the proof τ̄ is a transcript of an adversary making at most q queries to each oracle, and the hypothesis on 𝒯_q × K says nothing about other transcripts
--   - generalization: a keyed construction ℰ = (ℰ_k)_{k∈K}, oracle algorithms over the game's primitives, with its real and ideal systems → a KeyedGame: an arbitrary ideal system and an arbitrary family of conditional real systems indexed by the key; reason: every keyed construction's security game is such a family (the real system of key k is ℰ_k run on the primitives), so the Lean statement specializes to the paper's
--   - encoding: a system: a finite tuple of possibly randomized, possibly stateful oracles with joint randomness → a System: its transcript probabilities p(τ) (p ≥ 0, p([]) = 1, ∑_y p(τ ++ [(x, y)]) = p(τ)); reason: these are exactly the paper's p_b(τ), which determine every adversary's view; every system has them and every such function is a system
--   - reading: a finite tuple of oracles whose query and response sets the paper leaves implicit → a finite oracle set ι, finite query and response alphabets Q, R, each query addressed to the oracle oracleOf x; reason: the paper calls 𝒯_q 'the finite set', which needs finite alphabets; oracle-specific alphabets embed in common ones, a system giving probability 0 to responses an oracle cannot return
--   - encoding: the secret key as auxiliary information, an independent uniform dummy key in the ideal world → KeyedGame.realAux / idealAux: p_1(τ̄, k) = p_1^k(τ̄)/|K| and p_0(τ̄, k) = p_0(τ̄)/|K|; reason: these are the transcript probabilities of the paper's construction with the key appended
--   - encoding: p_1(τ)/p_0(τ) ≥ 1 − g(τ) for τ ∈ 𝒯 ∖ 𝒯_bad → (1 − g(τ)) · p_0(τ) ≤ p_1(τ) for attainable τ (p_0(τ) > 0) outside the bad set; reason: multiplying by p_0(τ) > 0; same condition, no division
--   - generalization: 𝒯_bad ⊆ 𝒯 (here 𝒯_q × K) → any set bad of (τ̄, k); reason: elements outside 𝒯 are never attained and carry weight p_0 = 0 in Δ and in every sum; the subset case is included
--   - encoding: a non-negative function g : 𝒯 → ℝ → g defined on all pairs, its non-negativity required only on attainable pairs in the hypothesis's transcript set; reason: g★ is only ever weighted by p_0 > 0 on those pairs, so values elsewhere are never used; the paper's g extends to such a function
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 10, proof of Theorem 3.1, Eq. (7)

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Oracles
import Definitions.Def_KeySchedules_Iterative_KeyedGames

namespace KeySchedules.Iterative

/-- Proof of Theorem 3.1, Eq. (7) (p. 10): let `ℰ` satisfy the hypotheses of Lemma 2.1 on
`𝒯_q × K` with the key as auxiliary information, and let `H : K' → K` be a key schedule. For
`ℰ ∘ H`, append the master key `k'` (uniform dummy in the ideal world), with transcript
probabilities `p^H_b(τ̄, k')`. Whenever `p^H_0(τ̄, k') > 0` (for `τ̄` with at most `q` queries
to each oracle),
`p^H_1(τ̄, k')/p^H_0(τ̄, k') = p_1(τ̄, H(k'))/p_0(τ̄, H(k')) ≥ 1 − g★(τ̄, H(k'))`. -/
theorem eq_7 {I : Interface} {K K' : Type} [Fintype K] [Nonempty K] [Fintype K']
    [Nonempty K'] (E : KeyedGame I K) (H : K' → K) (q : ℕ)
    (bad : Set (Transcript I × K)) (g : Transcript I × K → ℝ) (hcert : E.IsExpCert q bad g)
    (τ : Transcript I) (hτ : WithinQueries τ q) (k' : K')
    (hpos : 0 < (E.comp H).idealAux τ k') :
    (E.comp H).realAux τ k' / (E.comp H).idealAux τ k'
        = E.realAux τ (H k') / E.idealAux τ (H k') ∧
    E.realAux τ (H k') / E.idealAux τ (H k') ≥ 1 - gStar bad g (τ, H k') := by sorry

end KeySchedules.Iterative
