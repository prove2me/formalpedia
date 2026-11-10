-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_3_3
-- name    : KSATSingleFlip.Connect.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:07:24.370455+00:00
-- url     : https://prove2.me/theorems/287de3b8-bbb7-4eda-b0c9-0eff987ec322
-- title:
--   Lemma 3.3 — small complete forcing trees
-- statement:
--   Fix an assignment $\sigma$, let $k$ and $n\ge n_0(k)$ be sufficiently large, and put $s = \lceil(\ln k)^6\rceil$. If $\Phi\sim\mathrm{Pois1}(\sigma,\lambda)$ with
--   $$0\le\lambda\le \ln k + \ln\ln k + 1 + \frac{\ln\ln k + 1/2}{\ln k} - \frac{6(\ln\ln k)^2}{(\ln k)^2},$$
--   then with probability at least $1 - \exp(-n/(32k^{8s}))$, for every $\Psi\subseteq\Phi$ and $B\subseteq[n]$ with $|B|\le n/(16k^{2s})$, at least $n/2$ variables root complete forcing trees in $\Psi$ of size at most $(\ln k)^6$ avoiding $B$.
--
--   Differences from the source:
--   - encoding: Φ ∼ Pois1(σ, λ): independently for each v, Pois(λ) clauses forced at v → Pois(λn) clauses i.i.d. uniform among the proper k-clauses with exactly one σ-true literal; reason: Poisson superposition: same clause-multiset law; the event is invariant under reordering clauses
--   - encoding: Ψ ⊆ Φ and complete forcing trees in Ψ → a set I of clause positions of Φ; forcing trees of Φ with clauses in I, complete in Φ_I (HasSmallCFT); reason: sub-multisets of an indexed collection are exactly position sets
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 3.3, printed p. 14 (PDF 16)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 3.3 (small complete forcing trees; printed p. 14). `s = ⌈(ln k)^6⌉`. A sub-formula
`Ψ ⊆ Φ` is a set `I` of clause positions of `Φ`; "complete forcing trees in `Ψ`" are forcing trees
of `Φ` with clauses in `I`, complete in `Ψ`. -/
theorem lemma_3_3 :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ (σ : Fin n → Bool) (lam : ℝ),
      0 ≤ lam → lam ≤ loosenessLambda k →
        1 - Real.exp (-(n : ℝ) / (32 * (k : ℝ) ^ (8 * ⌈Real.log k ^ 6⌉₊))) ≤
          pois1Prob n k σ lam (fun Φ =>
            ∀ (I : Finset (Fin (ofList Φ).length)) (B : Finset (Fin n)),
              (B.card : ℝ) ≤ n / (16 * (k : ℝ) ^ (2 * ⌈Real.log k ^ 6⌉₊)) →
                (n : ℝ) / 2 ≤
                  ((Finset.univ.filter fun v =>
                    HasSmallCFT (ofList Φ) I σ v (Real.log k ^ 6) B).card : ℝ)) := by sorry

end KSATSingleFlip.Connect
