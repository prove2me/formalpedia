-- Prove2me | Theorems.Thm_GeomRescale_theorem_2_3
-- name    : GeomRescale.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:37.032035+00:00
-- url     : https://prove2.me/theorems/73ae16a6-07ee-417a-a8b3-37c7f01a4d57
-- title:
--   Theorem 2.3 (Fujishige): the minimum-norm point solves SFM
-- statement:
--   Let $f : 2^V \to \mathbb{R}$ be submodular with $f(\emptyset) = 0$. The problem
--
--   $$\min\Bigl\{\tfrac12 \|x\|_2^2 : x \in B(f)\Bigr\}$$
--
--   has a unique optimal solution $z$. The set $S^* = \{v \in V : z(v) < 0\}$ is the inclusionwise minimal minimizer of $f$, $f(S^*) = z^-(V)$, and $|f(S^*)| \le \sqrt{n}\, \|z\|_2$.
--
--   Lemma 3.8 uses this result to turn integrality of $f$ into a lower bound on the width of $F_\mu$.
--
--   Differences from the source:
--   - encoding: the unique optimal solution; the inclusionwise minimal minimizer → `∃!` and a universally quantified $z$; $S^*$ is a minimizer contained in every minimizer; reason: minimizers of a submodular function form a lattice, so the minimal one is the least
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Theorem 2.3, p.5

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_IsMinNormPoint

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Theorem 2.3, Fujishige (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Theorem 2.3, p.5): problem (6) has a unique optimal solution `z`.
The set `S* = {v ∈ V : z(v) < 0}` is the inclusionwise minimal minimizer of `f`, `f(S*) = z⁻(V)`,
and `|f(S*)| ≤ √n ‖z‖₂`.

**Formalization Note.** "Inclusionwise minimal minimizer" is: `S*` is a minimizer and is contained in
every minimizer. `z⁻(V) = ∑_v min {0, z(v)}`. The paper cites this result and does not prove it. -/
theorem theorem_2_3 {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0) :
    (∃! z, IsMinNormPoint f z) ∧
      ∀ z, IsMinNormPoint f z →
        let Sstar : Finset (Fin n) := Finset.univ.filter (fun v => z v < 0)
        (∀ T, f Sstar ≤ f T) ∧
          (∀ T, (∀ U, f T ≤ f U) → Sstar ⊆ T) ∧
          f Sstar = ∑ v, min 0 (z v) ∧
          |f Sstar| ≤ √(n : ℝ) * norm2 z := by sorry

end GeomRescale
