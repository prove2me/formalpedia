-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_7_1
-- name    : KSATSingleFlip.Connect.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:06:28.540936+00:00
-- url     : https://prove2.me/theorems/3fcaf9d7-8d90-42ec-8984-d23ee0829566
-- title:
--   Lemma 7.1 — Poisson comparison: $\Pr(\Phi^+\in\mathcal B\mid\sigma,\tau\in\Omega_\Phi)\le 15\sqrt m\,e^{4m\varepsilon_0^2}\Pr_{\mathrm{Pois}(m)}(\Phi^+\in\mathcal B)$
-- statement:
--   Let $\Phi,\Phi_{\mathrm{aux}}\sim\Phi(k,n,m)$ be independent and $\Phi^+ = \Phi\cup\{C\in\Phi_{\mathrm{aux}} : C(\sigma) = 0\text{ or }C(\tau) = 0\}$ (Algorithm 2, line 3). For an integer $m\ge1$, $\sigma,\tau\in\{0,1\}^n$, and any formula event $\mathcal B$ determined by the clause multiset,
--   $$\Pr(\Phi^+\in\mathcal B\mid\sigma,\tau\in\Omega_\Phi)\ \le\ 15\sqrt m\,e^{4m\varepsilon_0^2}\Pr_{\mathrm{Pois}(m)}(\Phi^+\in\mathcal B),$$
--   where under $\Pr_{\mathrm{Pois}(m)}$, $M\sim\mathrm{Pois}(m)$ and $\Phi^+\sim\Phi(k,n,M)$. The conditional probability is the ratio of the uniform probabilities over pairs $(\Phi,\Phi_{\mathrm{aux}})$.
--
--   Differences from the source:
--   - reading: no explicit range of k and n in the statement → ∃ k₀, ∀ k ≥ k₀, ∃ n₀, ∀ n ≥ n₀; reason: the model paragraph (p. 2) fixes the standing convention: "All results fix sufficiently large k and then sufficiently large n, uniformly over the stated density range"
--   - encoding: a formula event determined by the clause multiset → a predicate B on Multiset (ProperClause n k), applied to the clause multiset of Φ⁺; reason: an event determined by the multiset is a predicate of the multiset
--   - encoding: M ∼ Pois(m) and then M independent clauses → poisExp/poisProb: the series ∑_M e^{-m} m^M/M! · (uniform average over M-tuples of clauses); reason: same law; the integrands lie in [0,1], so the series converges
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 7.1, printed p. 53 (PDF 55)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.1 (Poisson comparison; printed p. 53). `Φ⁺ = Φ ∪ {C ∈ Φ_aux : C(σ) = 0 or C(τ) = 0}`
for independent `Φ, Φ_aux ∼ Φ(k, n, m)` (Algorithm 2, line 3); the conditional probability given
`σ, τ ∈ Ω_Φ` is compared with `Pr_{Pois(m)}`, under which `M ∼ Pois(m)` and `Φ⁺ ∼ Φ(k, n, M)`.
The event `B` is a predicate on the clause multiset. -/
theorem lemma_7_1 :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℕ, 1 ≤ m →
      ∀ (σ τ : Fin n → Bool) (B : Multiset (ProperClause n k) → Prop),
        let Φplus : Formula n k m → Formula n k m → Multiset (ProperClause n k) := fun F G =>
          toMultiset (List.ofFn F ++
            (List.ofFn G).filter fun C => !(decide (ClauseSat σ C.val ∧ ClauseSat τ C.val)))
        uprob (fun FG : Formula n k m × Formula n k m =>
            σ ∈ sols (ofFormula FG.1) ∧ τ ∈ sols (ofFormula FG.1) ∧ B (Φplus FG.1 FG.2)) /
          uprob (fun FG : Formula n k m × Formula n k m =>
            σ ∈ sols (ofFormula FG.1) ∧ τ ∈ sols (ofFormula FG.1)) ≤
        15 * Real.sqrt m * Real.exp (4 * m * eps0 k ^ 2) *
          poisProb (allClauses n k) m (fun l => B (toMultiset l)) := by sorry

end KSATSingleFlip.Connect
