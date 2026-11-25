-- Prove2me | Theorems.Thm_FracTruthSched_padding_sequence_limit
-- name    : FracTruthSched.padding_sequence_limit
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:23:49.281596+00:00
-- url     : https://prove2.me/theorems/d07e7a79-8533-4b1b-b341-b2c995c5f581
-- title:
--   Appendix A.2–A.4 — exact limit mechanism at rational and real graph inputs
-- statement:
--   Let $(A_K)$ be a `PaddingSequence` constructed from the original family $(R_m)$ and $\rho$. Then there is a single fractional mechanism $(x,P)$ on all nonnegative real graph inputs of $MC_\ell$ such that:
--
--   1. $(x,P)$ is feasible, truthful, eligible and symmetric within classes;
--   2. every edge with a unique zero-cost endpoint is allocated wholly to that endpoint;
--   3. the allocation has zero-type irrelevance;
--   4. for **every** $\rho'$ satisfying equation (3) for the original family (and in particular for $\rho$), every graph input $t$ satisfies $$\mathrm{Mech}_x(t)\le \rho' C(t).$$
--
--   The proof follows Claims 8–10. A diagonal compactness argument at rational graph inputs makes all inequalities exact; ceiling rounding $R_h(a)=\lceil h!a\rceil/h!$ and a common convergent subnet extend the mechanism to real inputs. Truthfulness is recovered from the incentive inequalities and the normalization $V(0;t_{-i})=0$, with $P_i(t)=t_i\cdot x_i(t)-V_i(t)$. The quantification over all $\rho'$ is the contrapositive form of the finite-witness claim.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Appendix A.2, Claim 8, p.26; Appendix A.3, Claim 9, p.27; Appendix A.4, Claim 10, p.27.

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasUniqueZeros
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_IsClassSymmetric
import Definitions.Def_FracTruthSched_PaddingSequence

set_option autoImplicit false

/-- **Limit of the padded mechanisms** (Anastasiadis et al., arXiv:2611.06642v1,
Appendix A.2–A.4, pp.25–27, Claims 8–10). Every `PaddingSequence` has an exact limit mechanism
on all real graph inputs: feasible, truthful, eligible, with unique zeros, zero-type irrelevance,
class symmetry, and the load bound for every ratio bound of the original family. -/
theorem FracTruthSched.padding_sequence_limit {n : ℕ} [NeZero n]
    (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (htruth : ∀ m, IsTruthfulOn Nonneg (R m))
    (ρ : ℝ) (hρ : ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ * opt t) (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (S : PaddingSequence R ρ ℓ) :
    ∃ M : FracMech n (CoreTask n ℓ),
      IsFeasibleOn IsGraphInput M ∧ IsTruthfulOn IsGraphInput M ∧
      (∀ t, IsGraphInput t → makespan M t ≤ ρ * C t) ∧
      (∀ ρ' : ℝ, (∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
          makespan (R m) t ≤ ρ' * opt t) →
        ∀ t, IsGraphInput t → makespan M t ≤ ρ' * C t) ∧
      IsEligible M ∧ HasUniqueZeros M ∧ HasZeroTypeIrrelevance M ∧ IsClassSymmetric M := by sorry
