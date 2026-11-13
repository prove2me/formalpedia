-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_Hypothesis78_chiRho_norm_sq_eq_card_ratio_mul
-- name    : OddOrder.Peterfalvi.S09.Hypothesis78.chiRho_norm_sq_eq_card_ratio_mul
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T07:46:05.445643+00:00
-- url     : https://prove2.me/theorems/06e59cca-b010-45f4-8e27-10f259fdaa9a
-- title:
--   Peterfalvi (7.8.c.ii): $\|\chi^\rho\|^2=(|A|/|L|)\,|(\beta,\chi)|^2$ for $\chi\perp S^\nu$
-- statement:
--   Let $G$ be a finite group, $A\subseteq G$, $L\le G$, and `H78 : Hypothesis78 G A L` a Peterfalvi (7.8) coherence datum with $\beta=$ `H78.beta`, family characters $\zeta_i=$ `hyp76.zeta i` and coherent extension $\nu=$ `H78.nu`. Let $\chi$ be an irreducible character of $G$ with $\langle\chi,\nu(\zeta_i)\rangle=0$ for all $i\ne$ `ind1H`. Then
--   $$\big\langle\chi^{\rho},\chi^{\rho}\big\rangle=\frac{|A|}{|L|}\,\langle\beta,\chi\rangle\,\overline{\langle\beta,\chi\rangle},$$
--   where $\chi^\rho=$ `chiRhoCF χ`.
--
--   This is Peterfalvi (7.8.c.ii), used for the norm estimates of (7.10).
--
--   **Formalization Note.** The `Fintype`/`Invertible` instances on $G$ and $L$ are explicit; `star` is complex conjugation and the right-hand side is a complex number.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean#L1055-L1111

import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_QuadraticTerm
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CoherenceFormula

namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

theorem chiRho_norm_sq_eq_card_ratio_mul (H78 : Hypothesis78 G A L)
    (χ : ClassFunction G ℂ) (hχ_irr : IsIrreducibleCharacter χ)
    (hχ_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner χ (H78.nu (H78.hyp76.zeta i)) = 0) :
    ClassFunction.inner (H78.hyp76.hyp71.chiRhoCF χ) (H78.hyp76.hyp71.chiRhoCF χ) =
      ((Nat.card A : ℂ) / (Nat.card L : ℂ)) *
        (ClassFunction.inner H78.beta χ *
          star (ClassFunction.inner H78.beta χ)) := by sorry

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09
