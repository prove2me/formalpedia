-- Prove2me | Theorems.Thm_MME_StothersFourth_fixedHash_budget_of_degree
-- name    : MME.StothersFourth.fixedHash_budget_of_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:49:57.957188+00:00
-- url     : https://prove2.me/theorems/e0a8f85d-aeaf-49da-a06c-1a474beace9b
-- title:
--   Fixed Stothers affine-hash selection from a degree margin
-- statement:
--   Let the full fixed-profile target family have size $VD_*$, and suppose every target-centered ambient completion star has degree at most $D$. For a three-term-progression-free set $S$ in the lower half of an odd prime modulus, assume the normalized collision margin
--
--   $$p^2\ell+3D_*D\le D_*|S|.$$
--
--   Then some affine hash state retains a vertex-closed family $E$ with
--
--   $$C(E)+V\ell\le T(E).$$
--
--   This is the deterministic averaging interface between the exact incidence sums and the target-surplus family.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equations (3.3)--(3.4), https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fixed_affine_hash
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.fixedHash_budget_of_degree
    (m p D Dstar : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp9 : 9 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (V loss : ℝ) (hV : 0 ≤ V)
    (hT : ((MME.StothersFourth.fixedHashAllTargetEdges m).card : ℝ) =
      V * (Dstar : ℝ))
    (hdeg : ∀ i : Fin 3,
      ∀ a ∈ MME.StothersFourth.fixedHashAllTargetEdges m,
      ((MME.StothersFourth.fixedHashMarginalUniverse m).filter
        (fun b ↦ b.1 i = a.1 i)).card ≤ D)
    (hmargin :
      (p : ℝ) ^ 2 * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ)) :
    ∃ E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m),
      MME.StothersFourth.FixedMarginalVertexClosed E ∧
        ((MME.StothersFourth.fixedTargetAmbientCollisions E).card : ℝ) +
            V * loss ≤
          ((MME.StothersFourth.fixedExactTargetEdges E).card : ℝ) := by
  sorry
