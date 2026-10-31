-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_1
-- name    : OfflineCensoredPricing.Identifiability.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:40.058984+00:00
-- url     : https://prove2.me/theorems/fcb17880-bccd-4d4c-a856-3b039f00c522
-- title:
--   Proposition 1, p. 9 — R_F is concave on [p̲, p̄] and p*_F = min{max{p†_F, p̲}, p̄}, for every F in the ambiguity set
-- statement:
--   Fix an instance satisfying the standing assumptions of the model, and let $F$ be any c.d.f. in the ambiguity set $\mathcal F$ (in particular $F = F_\xi$). Then the expected revenue $R_F(p) = p\,\mathbb E_F[\min\{\xi - bp, y\}]$ is concave in $p \in [\underline p,\bar p]$, and the optimal price is the projection of the unconstrained optimal price onto the feasible interval:
--   $$p^*_F = \mathrm{Proj}(p^\dagger_F, [\underline p,\bar p]) = \min\{\max\{p^\dagger_F, \underline p\}, \bar p\},$$
--   where $p^*_F$ and $p^\dagger_F$ are the largest maximizers of $R_F$ over $[\underline p,\bar p]$ and over $\mathbb R$.
--
--   This is the full-information problem: knowing $b$ and $F$, the optimal price solves a concave program. The projection form is used throughout §3 to compare optimal prices across the ambiguity set.
--
--   **Formalization Note** The paper states Proposition 1 for $F_\xi$ and extends it to every $F \in \mathcal F$ on p. 12 ("Similar to Proposition 1, $p^*_F = \mathrm{Proj}(p^\dagger_F, [\underline p,\bar p])$"); the statement covers both, since $F_\xi \in \mathcal F$.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 9, Proposition 1 (proof Appendix B.1, p. 35); extension to F ∈ 𝓕 p. 12

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Proposition 1** (p. 9), together with its extension to the ambiguity set ("Similar to
Proposition 1, `p*_F = Proj(p†_F, [p̲, p̄])`", p. 12). For any inventory level `y ≥ 0` and every law
`μ` of `ξ` in the ambiguity set (in particular `μ = μξ`), the expected revenue `R_F(q)` is concave
in `q ∈ [p̲, p̄]`, and the optimal price `p*_F` is the projection of `p†_F` onto `[p̲, p̄]`:
`p*_F = min{max{p†_F, p̲}, p̄}`. -/
theorem proposition_1 {K : ℕ} (I : Instance K) (hI : I.Standing) (μ : Measure ℝ) (hμ : μ ∈ Amb I) :
    ConcaveOn ℝ (Icc I.plo I.phi) (RF I μ) ∧
      pStar I μ = min (max (pDagger I μ) I.plo) I.phi := by sorry

end OfflineCensoredPricing.Identifiability
