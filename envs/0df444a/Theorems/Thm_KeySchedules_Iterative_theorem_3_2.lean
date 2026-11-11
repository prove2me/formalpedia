-- Prove2me | Theorems.Thm_KeySchedules_Iterative_theorem_3_2
-- name    : KeySchedules.Iterative.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:52:33.1552+00:00
-- url     : https://prove2.me/theorems/ea294af7-fc1c-4e9e-875f-2e3e6055ce70
-- title:
--   Theorem 3.2 — an iterative key schedule from one uniform public permutation keeps expectation-method security with probability ≥ 1 − e^{−λ}
-- statement:
--   Let $G$ be a finite abelian group, $S$ a nonempty finite set, $r\ge1$, and $\mathrm{Out}:S\to G$ balanced ($|\mathrm{Out}^{-1}(k)|=|S|/|G|$). Let $\mathcal E$ be a keyed construction with key space $G^r$ whose game satisfies the hypotheses of Theorem 3.1: those of Lemma 2.1 on $\mathcal T_q\times G^r$ with the secret key as auxiliary information, with data $(\mathcal T_{\mathrm{bad}},g)$, where $\mathcal T_q$ is the set of query-response transcripts attainable in the ideal world with at most $q$ queries to each oracle. For a permutation $\varphi$ of $S$ let $\mathrm{KS}_\varphi(s)=(\mathrm{Out}(\varphi(s)),\dots,\mathrm{Out}(\varphi^r(s)))$. Then for every $\lambda>0$, a uniform permutation $\varphi$ of $S$ satisfies, with probability at least $1-e^{-\lambda}$,
--   $$\mathrm{Adv}_{\mathcal E\circ\mathrm{KS}_\varphi}(\mathcal A)\le(e-1)\,\Delta_{\mathcal E}(\mathcal A)+\frac{2r^2}{|S|}\bigl(\log|\mathcal T_q|+\lambda+1\bigr)$$
--   for every adversary $\mathcal A$ making at most $q$ queries to each oracle of the original game, where $\Delta_{\mathcal E}(\mathcal A)=\mathbb E[g^\star(\bar\Theta_0,k)]$ ($\bar\Theta_0$ the ideal transcript, $k$ uniform in $G^r$ and independent). One permutation serves all adversaries at once, and the adversary may depend on $\varphi$.
--
--   The theorem shrinks the master-key space from $G^r$ to $S$ while losing at most a factor $e-1$ and an additive $O(r^2(\log|\mathcal T_q|+\lambda)/|S|)$; applied to key-alternating ciphers it yields Corollary 3.1.
--
--   Differences from the source:
--
--   - generalization: a keyed construction ℰ = (ℰ_k)_{k∈K}, oracle algorithms over the game's primitives, with its real and ideal systems → a KeyedGame: an arbitrary ideal system and an arbitrary family of conditional real systems indexed by the key; reason: every keyed construction's security game is such a family (the real system of key k is ℰ_k run on the primitives), so the Lean statement specializes to the paper's
--   - encoding: a system: a finite tuple of possibly randomized, possibly stateful oracles with joint randomness → a System: its transcript probabilities p(τ) (p ≥ 0, p([]) = 1, ∑_y p(τ ++ [(x, y)]) = p(τ)); reason: these are exactly the paper's p_b(τ), which determine every adversary's view; every system has them and every such function is a system
--   - reading: a finite tuple of oracles whose query and response sets the paper leaves implicit → a finite oracle set ι, finite query and response alphabets Q, R, each query addressed to the oracle oracleOf x; reason: the paper calls 𝒯_q 'the finite set', which needs finite alphabets; oracle-specific alphabets embed in common ones, a system giving probability 0 to responses an oracle cannot return
--   - reading: every adversary (computationally unbounded, possibly randomized, adaptive) → an Adversary: a finite mixture, with probability weights, of deterministic strategies (next query or stop, output bit), probabilities and Δ averaged over the mixture; reason: a randomized adversary is a distribution over deterministic strategies; with finite alphabets and a query bound there are finitely many behaviours, so finite mixtures cover all of them; a single strategy is the mixture with one weight 1
--   - encoding: making at most q queries to each oracle → Adversary.WithinBudget q: no strategy of the mixture ever asks a (q+1)-st query to any oracle, whatever the responses; reason: the per-oracle budget of the paper; it also makes every run stop
--   - encoding: the secret key as auxiliary information, an independent uniform dummy key in the ideal world → KeyedGame.realAux / idealAux: p_1(τ̄, k) = p_1^k(τ̄)/|K| and p_0(τ̄, k) = p_0(τ̄)/|K|; reason: these are the transcript probabilities of the paper's construction with the key appended
--   - encoding: p_1(τ)/p_0(τ) ≥ 1 − g(τ) for τ ∈ 𝒯 ∖ 𝒯_bad → (1 − g(τ)) · p_0(τ) ≤ p_1(τ) for attainable τ (p_0(τ) > 0) outside the bad set; reason: multiplying by p_0(τ) > 0; same condition, no division
--   - encoding: with probability at least 1 − e^{−λ} over a uniform φ, the bound holds for every adversary → the set of φ for which some adversary within the budget violates the bound has at most e^{−λ} · |S|! elements; reason: uniform probability on Equiv.Perm S as a counting ratio of the failure event; the adversary is chosen after φ, so one φ serves every adversary
--   - encoding: |G| ∣ |S| and |Out⁻¹(k)| = |S|/|G| for every k → IsBalanced Out: |Out⁻¹(k)| · |G| = |S| for every k; reason: equivalent; the product form implies the divisibility, so it is not a separate hypothesis
--   - encoding: rounds and coordinates 1, …, r → Fin r, index i standing for round i + 1; reason: index base only
--   - generalization: 𝒯_bad ⊆ 𝒯 (here 𝒯_q × K) → any set bad of (τ̄, k); reason: elements outside 𝒯 are never attained and carry weight p_0 = 0 in Δ and in every sum; the subset case is included
--   - encoding: a non-negative function g : 𝒯 → ℝ → g defined on all pairs, its non-negativity required only on attainable pairs in the hypothesis's transcript set; reason: g★ is only ever weighted by p_0 > 0 on those pairs, so values elsewhere are never used; the paper's g extends to such a function
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 13, Theorem 3.2, Eq. (13)

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Oracles
import Definitions.Def_KeySchedules_Iterative_KeyedGames
import Definitions.Def_KeySchedules_Iterative_Schedule

namespace KeySchedules.Iterative

/-- Theorem 3.2 (iterative key schedules, p. 13). Let `ℰ` be a keyed construction with key
space `G^r` whose game satisfies the hypotheses of Theorem 3.1: the hypotheses of Lemma 2.1 on
`𝒯_q × G^r` with the key as auxiliary information, with data `(𝒯_bad, g)`. For every `λ > 0`,
for a uniform permutation `φ` of `S`, with probability at least `1 − e^{−λ}`, every adversary
making at most `q` queries to each oracle satisfies
`Adv_{ℰ∘KS_φ}(A) ≤ (e − 1) Δ_ℰ(A) + (2r²/|S|)(log |𝒯_q| + λ + 1)`.
Stated as: the permutations `φ` for which some such adversary violates the bound number at
most `e^{−λ} |S|!`. -/
theorem theorem_3_2 {I : Interface} {S G : Type} [AddCommGroup G] [Fintype G] [Fintype S]
    [DecidableEq S] [Nonempty S] (r : ℕ) (hr : 1 ≤ r) (Out : S → G) (hOut : IsBalanced Out)
    (E : KeyedGame I (Fin r → G)) (q : ℕ) (bad : Set (Transcript I × (Fin r → G)))
    (g : Transcript I × (Fin r → G) → ℝ) (hcert : E.IsExpCert q bad g)
    (lam : ℝ) (hlam : 0 < lam) :
    ({φ : Equiv.Perm S | ∃ A : Adversary I, A.WithinBudget q ∧
        (E.comp (KS Out r φ)).adv A >
          (Real.exp 1 - 1) * E.delta bad g A
            + 2 * (r : ℝ) ^ 2 / (Fintype.card S : ℝ)
              * (Real.log ((Tq E.ideal q).ncard : ℝ) + lam + 1)}.ncard : ℝ)
      ≤ Real.exp (-lam) * (Fintype.card (Equiv.Perm S) : ℝ) := by sorry

end KeySchedules.Iterative
