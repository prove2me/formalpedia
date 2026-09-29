-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime
-- name    : ModularCurve.NodeLocalized.exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/09fc465d-9b3d-5eaa-a72d-9229357ce298
-- title:
--   Enlarging the coefficient field to lift a residue value
-- statement:
--   Let $p$ be a prime, let $A^\flat$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that the image of $p$ lies in the nonunits of $A^\flat$, and let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite over $\mathbb{Q}$. Write $A^\flat \cap K$ for the coefficient subring, the intersection of $A^\flat$ with $K$ inside $\overline{\mathbb{Q}}$, and let reduction on it be the residue map of the local ring $A^\flat$ restricted along the inclusion $A^\flat \cap K \hookrightarrow A^\flat$. Assume $\varpi^\flat \in A^\flat \cap K$ is such that an element of $A^\flat \cap K$ reduces to $0$ precisely when it is a multiple of $\varpi^\flat$, and that $p = (\varpi^\flat)^{e_0}\varepsilon$ in $A^\flat \cap K$ for some $e_0 \in \mathbb{N}$ and some unit $\varepsilon$. Then for every element $j_0$ of the residue field of $A^\flat$ there exist an intermediate field $K'$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$ and containing $K$, an element $x_w \in A^\flat \cap K'$ reducing to $j_0$, an element $\varpi' \in A^\flat \cap K'$ such that an element of $A^\flat \cap K'$ reduces to $0$ precisely when it is a multiple of $\varpi'$, an integer $r \ge 1$ and units $u, \varepsilon'$ of $A^\flat \cap K'$ with $\varpi^\flat = (\varpi')^{r}u$ (as an equality in $\overline{\mathbb{Q}}$) and $p = (\varpi')^{r e_0}\varepsilon'$ in $A^\flat \cap K'$.
--
--   This is the standard bookkeeping for an extension of discrete valuation rings: passing to a larger number field multiplies the valuation of a uniformiser by the local ramification index $r$, so a relation $p = (\varpi^\flat)^{e_0}\varepsilon$ becomes $p = (\varpi')^{re_0}\varepsilon'$, no unramifiedness of $K'/K$ being claimed. It serves to enlarge the coefficient number field so that a prescribed residue value (for instance a $j$-invariant in the residue field of $A^\flat$) becomes the reduction of an actual coefficient, and is used in the computation of crossing exponents at places of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime
    (p : ℕ) [Fact p.Prime] (Ab : ValuationSubring (AlgebraicClosure ℚ)) (hAb : Ab.LiesOverPrime p)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (ϖb : ↥(coeffSubring Ab K))
    (hϖb : ∀ d : ↥(coeffSubring Ab K), redRestrict (IsLocalRing.residue ↥Ab) K d = 0 ↔ ∃ d', d = ϖb * d')
    (e₀ : ℕ) (ε : ↥(coeffSubring Ab K)) (hε : IsUnit ε)
    (hpε : ((p : ℕ) : ↥(coeffSubring Ab K)) = ϖb ^ e₀ * ε)
    (j₀ : IsLocalRing.ResidueField ↥Ab) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K') (_ : K ≤ K')
      (xw : ↥(coeffSubring Ab K')) (_ : redRestrict (IsLocalRing.residue ↥Ab) K' xw = j₀)
      (ϖ' : ↥(coeffSubring Ab K'))
      (_ : ∀ d : ↥(coeffSubring Ab K'), redRestrict (IsLocalRing.residue ↥Ab) K' d = 0 ↔ ∃ d', d = ϖ' * d')
      (r : ℕ) (_ : 1 ≤ r) (u : ↥(coeffSubring Ab K')) (_ : IsUnit u)
      (_ : (ϖb : AlgebraicClosure ℚ) = ((ϖ' ^ r * u : ↥(coeffSubring Ab K')) : AlgebraicClosure ℚ))
      (ε' : ↥(coeffSubring Ab K')) (_ : IsUnit ε'),
      ((p : ℕ) : ↥(coeffSubring Ab K')) = ϖ' ^ (r * e₀) * ε' := by sorry
