-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_proposition_3
-- name    : KeskinLiSong.DDPO.proposition_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:49:39.081306+00:00
-- url     : https://prove2.me/theorems/d255707d-3621-40f5-a959-f5eece237d2f
-- title:
--   Proposition 3 — general exponential-family MLE
-- statement:
--   Let the d-dimensional exponential-family parameter phi lie in compact Phi; the family may be nonidentifiable and its reference measure may encode either densities or masses. Suppose the score has a uniformly finite ell-th moment for ell>d. The printed positive delta is retained although unused. K5,K6 precede all positive sample sizes k, including k=1. The projected unconstrained MLE exists as a measurable selection and the bound holds for every such selection.
--
--   $$
--   \mathbb P_\phi\!\left(\|\widehat\phi_k-\phi\|^2\ge K_5\frac{\log k}{k}\right)\le\frac{K_6}{k}\quad(k\ge1).
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   PROPOSITION 3. Assume that sup_{φ∈Φ} E_φ‖∇_φ log f_z(z;φ)‖^ℓ < ∞ for some ℓ>d. Then for any δ>0
--   there exist positive constants K_5 and K_6 such that
--   P_φ{‖φ̂_k−φ‖² ≥ K_5 log k/k} ≤ K_6/k, (24)
--   where φ̂_k is the projection onto Φ of the maximum likelihood estimator of φ, based on k i.i.d. observations
--   from f_Z(z;φ), and P_φ{z_1∈dẑ_1,...,z_k∈dẑ_k}=∏_{i=1}^k f_Z(ẑ_i;φ)dẑ_i.
--
--   Differences from the source:
--   - encoding: the named policy, optimizer or estimator is used as a defined mathematical object → operational existence, integrability and genuine attainment are explicit content where required; reason: partial constructions are not silently filled by arbitrary defaults or assumed as a premise of the goal
--   - encoding: exponential-family density f_Z with displayed integration dz → an explicit reference measure supports both densities and mass functions; reason: the source explicitly includes Poisson; this avoids excluding discrete families
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Proposition 3, printed p. 22 (PDF p. 22)

import Definitions.Def_KeskinLiSong_DDPO_TailEvents

open MeasureTheory ProbabilityTheory

namespace KeskinLiSong.DDPO

theorem proposition_3 (d : ℕ) (F : ExponentialFamily d) (phi : Vector d)
    (hphi : phi ∈ F.parameterSet) (ell : ℝ) (hmoment : ScoreMoment F ell)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ K5 K6 : ℝ, 0 < K5 ∧ 0 < K6 ∧ ∀ k : ℕ, 1 ≤ k →
      (∃ estimate : (Fin k → ℝ) → Vector d,
        Measurable estimate ∧ ∀ᵐ z ∂iidLaw (F.law phi) k,
          F.ProjectedMLE (List.ofFn z) (estimate z)) ∧
      (∀ estimate : (Fin k → ℝ) → Vector d, Measurable estimate →
        (∀ᵐ z ∂iidLaw (F.law phi) k, F.ProjectedMLE (List.ofFn z) (estimate z)) →
        ((iidLaw (F.law phi) k) {z | K5 * Real.log k / k ≤ ‖estimate z - phi‖ ^ 2}).toReal
          ≤ K6 / k) := by sorry

end KeskinLiSong.DDPO
