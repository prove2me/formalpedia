-- Prove2me | Theorems.Thm_FulfillFlex_lemma_8
-- name    : FulfillFlex.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:14.218786+00:00
-- url     : https://prove2.me/theorems/561c0301-a9f9-42b7-b47e-b27597665d06
-- title:
--   Lemma 8, p.50 — an optimal DLP solution that spills only after covering local demand
-- statement:
--   Suppose Assumption 2 holds (and the standing Assumption 1). Then the DLP (5) has an optimal solution $(f^*,l^*)$ such that for all $j\neq j'$,
--
--   $$
--   f^*_{jj'}>0\ \Longrightarrow\ f^*_{jj}=m_j,
--   $$
--
--   where $m_j=T\mu_j$ in the paper. In words, a DC ships to other DCs only after its own mean demand is covered. This is what makes the protection of local demand compatible with the local no-holdback rule.
--
--   Differences from the source:
--   - generalization: right side Tμ → every right side m ≥ 0 and r ≥ 0; reason: the paper's statement is the instance m = T • μ, r = T • b
--   - reading: links A, a set of ordered pairs (p.5) → (j, j) ∈ A for every j; reason: local fulfillment is always available and (5) forces f_jj = 0 off A; Assumption 2 is claimed for Example 1, whose links (1,2), (2,1) force (1,1) ∈ A by transitivity
--   - reading: Proposition 3 and Lemma 8 say "under Assumption 2" → Assumption 1 is also a hypothesis; reason: Assumption 1 is standing from p.6, and the proof uses it (Lemma 8, Case 2; the bound on local fulfillment; linear scaling)
--   - encoding: "there exists an optimal solution" → existence of a pair (f, l) that is feasible and minimal among feasible pairs; reason: the paper takes attainment of the minimum for granted; here it is part of the claim
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Lemma 8, p.50

import Mathlib
import Definitions.Def_FulfillFlex_Assumption1
import Definitions.Def_FulfillFlex_Assumption2
import Definitions.Def_FulfillFlex_IsDLPOptimal

namespace FulfillFlex

/-- **Lemma 8 (spillover only after local demand is covered).**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Lemma 8, p.50: under Assumption 2 there
is an optimal solution `f*` of (5) such that `f*_{jj'} > 0` for `j' ≠ j` implies `f*_jj = Tμ_j`.

**Formalization Note** The statement holds for every right side `m ≥ 0` and `r ≥ 0`, the paper's
being `m = T • μ`. Assumption 1 is standing from p.6, and the links contain the diagonal. The
existence of a minimizer is part of the claim. -/
theorem lemma_8 {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (p : DC N → ℝ)
    (α : DC N → unitInterval) (m r : DC N → ℝ) (hdiag : ∀ j, (j, j) ∈ A)
    (hA1 : Assumption1 A c p) (hA2 : Assumption2 A c) (hm : ∀ j, 0 ≤ m j) (hr : ∀ j, 0 ≤ r j) :
    ∃ f l, IsDLPOptimal A c p α m r f l ∧ ∀ j j', j' ≠ j → 0 < f j j' → f j j = m j := by sorry

end FulfillFlex
