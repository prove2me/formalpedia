-- Prove2me | Theorems.Thm_FulfillFlex_lemma_8_consequence
-- name    : FulfillFlex.lemma_8_consequence
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:06.879455+00:00
-- url     : https://prove2.me/theorems/f837927a-96c0-44f5-9cae-1b6b1be2ece7
-- title:
--   Appendix B.3.1, p.51 — consequence of Lemma 8: $f^*_{jj}<T\mu_j$ implies $f^*_{jj}=r_j$
-- statement:
--   Under the hypotheses of Lemma 8, the DLP (5) has an optimal solution with both properties: $f^*_{jj'}>0$ for some $j'\ne j$ implies $f^*_{jj}=m_j$, and
--
--   $$
--   f^*_{jj}<m_j\ \Longrightarrow\ f^*_{jj}=r_j,
--   $$
--
--   where $m_j=T\mu_j$ in the paper. In words, the optimal solution leaves demand unfilled locally at DC $j$ only after using all the inventory of DC $j$ for local fulfillment. This is the structured solution from which the spillover limits of Proposition 3 are built.
--
--   Differences from the source:
--   - reading: "we can assume without loss of optimality" that f∗jj = r∗j if f∗jj < Tµj → one optimal solution has both this property and that of Lemma 8; reason: this is the form the rest of the proof consumes
--   - generalization: right side Tμ → every right side m ≥ 0 and r ≥ 0; reason: the paper's statement is the instance m = T • μ, r = T • b
--   - reading: links A, a set of ordered pairs (p.5) → (j, j) ∈ A for every j; reason: local fulfillment is always available and (5) forces f_jj = 0 off A; Assumption 2 is claimed for Example 1, whose links (1,2), (2,1) force (1,1) ∈ A by transitivity
--   - reading: Proposition 3 and Lemma 8 say "under Assumption 2" → Assumption 1 is also a hypothesis; reason: Assumption 1 is standing from p.6, and the proof uses it (Lemma 8, Case 2; the bound on local fulfillment; linear scaling)
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, p.51

import Mathlib
import Definitions.Def_FulfillFlex_Assumption1
import Definitions.Def_FulfillFlex_Assumption2
import Definitions.Def_FulfillFlex_IsDLPOptimal

namespace FulfillFlex

/-- **Consequence of Lemma 8.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, p.51: "First, we prove a
consequence of the condition in Lemma 8: if f∗jj < Tµj, then f∗jj = r∗j", with "we can assume
without loss of optimality that f∗jj = r∗j if f∗jj < Tµj". One optimal solution of (5) has both
properties.

**Formalization Note** The statement holds for every right side `m ≥ 0` and `r ≥ 0`, the paper's
being `m = T • μ`. Assumption 1 is standing from p.6, and the links contain the diagonal. -/
theorem lemma_8_consequence {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (p : DC N → ℝ)
    (α : DC N → unitInterval) (m r : DC N → ℝ) (hdiag : ∀ j, (j, j) ∈ A)
    (hA1 : Assumption1 A c p) (hA2 : Assumption2 A c) (hm : ∀ j, 0 ≤ m j) (hr : ∀ j, 0 ≤ r j) :
    ∃ f l, IsStructuredOptimal A c p α m r f l := by sorry

end FulfillFlex
