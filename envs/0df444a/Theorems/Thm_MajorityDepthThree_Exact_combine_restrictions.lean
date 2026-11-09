-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_combine_restrictions
-- name    : MajorityDepthThree.Exact.combine_restrictions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:38.760669+00:00
-- url     : https://prove2.me/theorems/b8fca241-06bf-4378-ad4d-2ac4b1f1a131
-- title:
--   Lemma 5.12 — combined coverage and normalized cost
-- statement:
--   Let $\mathcal A$ be a set system on $V$, $n=|V|$, and let $\rho_1,\ldots,\rho_k$ be restrictions. For each $S\in\mathcal A$, let $I(S)$ index its compatible restrictions. Suppose $\lambda_i\ge0$ and
--
--   $$\sum_{i\in I(S)}\lambda_i q^{|S\cap\operatorname{supp}^-(\rho_i)|}\ge1\quad(S\in\mathcal A).$$
--
--   For feasible residual weights $f_i$, the combined weight $f=\sum_i\lambda_iL_{\rho_i}(f_i)$ is feasible and satisfies
--
--   $$\operatorname{cost}(f)=\sum_i\lambda_i r^{|\operatorname{supp}^+(\rho_i)|}\operatorname{cost}(f_i).$$
--
--   Furthermore, for any real $\omega_i$ satisfying $C_{\mathcal A_{\rho_i}}\le\omega_i p^{n-|\operatorname{supp}(\rho_i)|}$ for every $i$,
--
--   $$\frac{C_{\mathcal A}}{p^n}\le\sum_i\frac{\lambda_i\omega_i r^{|\operatorname{supp}^+(\rho_i)|}}{p^{|\operatorname{supp}(\rho_i)|}}=\sum_i\lambda_i\omega_i2^{-|\operatorname{supp}^+(\rho_i)|}q^{|\operatorname{supp}^-(\rho_i)|}.$$
--
--   All three conclusions are retained. The parameters are the fixed Section 5 values, and every $C$ is the actual covering minimum. This is the common statement used to combine residual budgets.
--
--   Differences from the source:
--   - encoding: A finite ground set V and its subsets → Finite subsets V of a variable type, with finite families of subsets; reason: Every source instance has this representation; all assignments and ambient isolated variables are retained
--   - encoding: Restrictions and the augmented restrictions of Note 5.3 → Disjoint positive and negative supports contained in V, plus optional clauses on unset variables; reason: An empty collection of extra clauses gives ordinary restrictions; residual families and lifted weights use strong consistency, while compatibility remains weaker
--   - encoding: Indices 1 through k → Fin k; reason: This changes only index names; the empty sum is allowed
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.14, Lemma 5.12 (proof continues p.15)

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false
open scoped Classical

namespace MajorityDepthThree.Exact

theorem combine_restrictions {α : Type} [DecidableEq α] (V : Finset α)
    (A : Family α) (hA : ∀ S ∈ A, S ⊆ V) (k : ℕ)
    (ρ : Fin k → Restriction V) (coeff : Fin k → ℝ)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hc : ∀ S ∈ A,
      1 ≤ ∑ i ∈ Finset.univ.filter (fun i => Compatible A (ρ i) S),
        coeff i * q ^ (S ∩ (ρ i).neg).card)
    (f : Fin k → Weight α) (hf : ∀ i, CoverFeasible (residual A (ρ i)) q (f i)) :
    CoverFeasible A q (combinedWeight ρ coeff f) ∧
    cost A r (combinedWeight ρ coeff f) =
      ∑ i, coeff i * r ^ (ρ i).pos.card * cost (residual A (ρ i)) r (f i) ∧
    ∀ omega : Fin k → ℝ,
      (∀ i, coverValue (residual A (ρ i)) r q ≤ omega i * p ^ (V.card - (ρ i).support.card)) →
      coverValue A r q / p ^ V.card ≤
        ∑ i, coeff i * omega i * r ^ (ρ i).pos.card / p ^ (ρ i).support.card ∧
      (∑ i, coeff i * omega i * r ^ (ρ i).pos.card / p ^ (ρ i).support.card) =
        ∑ i, coeff i * omega i * (2 : ℝ) ^ (-((ρ i).pos.card : ℤ)) * q ^ (ρ i).neg.card := by sorry

end MajorityDepthThree.Exact
