-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_lemma_4_4
-- name    : LowRandomnessDP.KNorm.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:08.073853+00:00
-- url     : https://prove2.me/theorems/5f9e1b9f-625e-42bb-8234-4da035266247
-- title:
--   Lemma 4.4 — cell-distance and full norm error
-- statement:
--   Fix a coefficient $B\ge1$ in $k_d(\ell)\le B d\log(d+1)e^{d/\ell}$. There is a positive threshold $S_0$ such that for every fixed $S\ge S_0$ there are positive constants $C_\Delta,C_e$, uniform in the instance, with the following property. For every $d\ge2$, admissible $K$, $\varepsilon>0$ and MSSP at scale $\rho=Sd/\varepsilon$ obeying this envelope, Algorithm 2 has a normalized cell law $p_v$ for every real vector $v$, and
--
--   $$\mathbb E_{p_v}[\Delta_P(v)]\le C_\Delta\frac{\log d}{\varepsilon},\qquad
--   \mathbb E_{p_v}[\|r(P)-v\|_K]\le C_e\frac d\varepsilon.$$
--
--   The second bound includes representative displacement, not just distance to the cell.
--
--   Differences from the source:
--   - encoding: real vectors and their K-norm → Fin d → ℝ with the Minkowski gauge of the exact compact convex symmetric absorbing disk; reason: coordinate encoding preserves all real vectors and all source norms; compactness excludes nontrivial linear subspaces
--   - encoding: probabilities and nonnegative expectations → ENNReal sums and mass-one PMFs, with finite positive normalizers proved in the conclusion; reason: retains divergent expectations as infinity and prevents divergent real sums from becoming zero
--   - encoding: a sufficiently large absolute scale C and the absolute MSSP O coefficient → for each fixed B≥1, a threshold S₀, and for every fixed S≥S₀ uniform error constants; reason: B and S are chosen before all instance parameters; this makes the dependence on fixed absolute constants explicit and lets the utility and entropy statements share one scale
--   - generalization: the chosen Theorem 3.2 partition at v=f(X) → every MSSP obeying the same envelope and every v; reason: the estimates use only the stated MSSP counts; the actual construction and every query value specialize to this statement
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Lemma 4.4, PDF page 16 / printed page 14 (proof continues PDF 17 / printed 15)

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem lemma_4_4 :
    ∀ B : ℝ, 1 ≤ B → ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S →
      ∃ Cdist Ce : ℝ, 0 < Cdist ∧ 0 < Ce ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ K : Set (Vec d), IsBody K →
      ∀ ε : ℝ, 0 < ε → ∀ (P : CellPartition d) (k : ℕ → ℕ),
      IsMSSP K P k (S * d / ε) → RateBound B d k →
      ∀ v : Vec d, Normalizable ε (fun c => cellDistance K P c v) ∧
        ∃ p : PMF P.Cell, (∀ c, p c = gibbsMass ε (fun a => cellDistance K P a v) c) ∧
          cellExpectation P p (fun c => cellDistance K P c v) ≤
            ENNReal.ofReal (Cdist * Real.log d / ε) ∧
          cellExpectation P p (fun c => kNorm K (P.representative c - v)) ≤
            ENNReal.ofReal (Ce * d / ε) := by sorry

end LowRandomnessDP.KNorm
