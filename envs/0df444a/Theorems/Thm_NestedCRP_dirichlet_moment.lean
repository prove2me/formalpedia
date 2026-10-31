-- Prove2me | Theorems.Thm_NestedCRP_dirichlet_moment
-- name    : NestedCRP.dirichlet_moment
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:38.867241+00:00
-- url     : https://prove2.me/theorems/613763c1-111e-481f-9126-f1ff5abce4e6
-- title:
--   Dirichlet moments as a ratio of normalizing constants
-- statement:
--   For a nonempty finite index set, parameters $\alpha_i>0$, exponents $n_i\in\mathbb N$ and $U\sim\mathrm{Dir}(\alpha)$,
--
--   $$
--   \mathbb E\Bigl[\prod_i U_i^{n_i}\Bigr]=\frac{\Gamma\bigl(\sum_i\alpha_i\bigr)}{\prod_i\Gamma(\alpha_i)}\cdot\frac{\prod_i\Gamma(n_i+\alpha_i)}{\Gamma\bigl(\sum_i n_i+\sum_i\alpha_i\bigr)}.
--   $$
--
--   Integrating the multinomial parameters out of a node gives this ratio of Dirichlet normalizers, which is the source of the Gamma factors in Eq. (4).
--
--   Differences from the source:
--   - generalization: the symmetric prior with parameter η, and a ratio of normalizing constants stated in words → general parameters α, with the ratio written out; reason: the source's case is α_i = η
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §5.2, p.7:17

import Mathlib
import Definitions.Def_NestedCRP_dirichletMeasure

namespace NestedCRP

/-- The moments of the Dirichlet law, a ratio of its normalizing constants:
`E ∏_v U_v^{n_v} = Γ(∑ α_v) / ∏_v Γ(α_v) · ∏_v Γ(n_v + α_v) / Γ(∑ n_v + ∑ α_v)`.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.2, p.7:17.

**Formalization Note** Stated for general `α`; the paper's topic prior is `α_v = η`. -/
theorem dirichlet_moment {ι : Type*} [Fintype ι] [Nonempty ι] (α : ι → ℝ) (hα : ∀ i, 0 < α i)
    (n : ι → ℕ) :
    ∫ U, ∏ i, U i ^ n i ∂dirichletMeasure α =
      Real.Gamma (∑ i, α i) / (∏ i, Real.Gamma (α i)) *
        ((∏ i, Real.Gamma ((n i : ℝ) + α i)) / Real.Gamma ((∑ i, (n i : ℝ)) + ∑ i, α i)) := by sorry

end NestedCRP
