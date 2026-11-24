-- Prove2me | Theorems.Thm_LinearIdentifiability_likelihood_ratio_identity
-- name    : LinearIdentifiability.likelihood_ratio_identity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:35:45.513996+00:00
-- url     : https://prove2.me/theorems/272d7270-d8db-4807-aec4-63b5669a868b
-- title:
--   Theorem 1, eqs. (5)-(7): equal likelihood ratios give the difference identity
-- statement:
--   Let $p_{\mathcal D}$ be a data distribution as in Section 2.1, and let $(f',g')$ and $(f^*,g^*)$ be two models of the form (1) with $p'=p^*$ on the data. Let $(x,S)$ occur in the data and let $y_A,y_B\in S$. Then the likelihood ratios agree,
--
--   $$\frac{p'(y_A\mid x,S)}{p'(y_B\mid x,S)}=\frac{p^*(y_A\mid x,S)}{p^*(y_B\mid x,S)},$$
--
--   and, the normalising constants cancelling,
--
--   $$(g'(y_A)-g'(y_B))^\top f'(x)=(g^*(y_A)-g^*(y_B))^\top f^*(x).$$
--
--   This is the identity (7) on which the identifiability of $f$ rests.
--
--   **Formalization Note** The paper writes the support condition as $p_{\mathcal D}(x,y_B,y_B)>0$ (a typo); it is stated here as: $y_A$ and $y_B$ lie in one candidate set $S$ with $p_{\mathcal D}(x,S)>0$, which is what the proof uses.
-- source:
--   Roeder, Metz and Kingma, On Linear Identifiability of Learned Representations, arXiv:2007.00810v3 (2020), Section 3.2, proof of Theorem 1, eqs. (5)-(7), p. 4

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix

namespace LinearIdentifiability

theorem likelihood_ratio_identity {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (x : X) (S : Finset Y) (hS : IsSupported pD x S) (yA yB : Y) (hA : yA ∈ S) (hB : yB ∈ S) :
    modelProb f' g' x S yA / modelProb f' g' x S yB =
        modelProb fstar gstar x S yA / modelProb fstar gstar x S yB ∧
      (g' yA - g' yB) ⬝ᵥ f' x = (gstar yA - gstar yB) ⬝ᵥ fstar x := by sorry

end LinearIdentifiability
