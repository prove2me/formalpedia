-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
-- name    : ModularCurve.JHNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/4de124ce-c610-589f-bd05-a80cd5c9a854
-- title:
--   Multiplication by m on a base-changed level-Γ_H(M) Néron object
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A \subseteq \overline{\mathbb{Q}}$ satisfying `A.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ lies in the nonunits of $A$, whose residue field is of characteristic $p$ and algebraically closed. Let $\Lambda$ be a term of `JHNeronObjectAtP.LevelData p M H hpM A`: a morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` compatible with the marked points (`barPt A` followed by $\sigma_A$ is `genPt p`), together with a scheme $X$ over `base p`, a relative group law on it over `baseRing p`, a bijection between $J_H(M/p)$ at the inflated subgroup and the sections over the generic point, and a bijection between $\mathrm{Pic}^0$ of the residue-field curve and the sections over `resPt A` followed by $\sigma_A$. Let $O$ be a level-$\Gamma_H(M)$ Néron object at $p$ for these data, consisting of a scheme $G$ with a structure morphism $g \colon G \to$ `base p`, a relative group law $L = O.L$ on $g$ over `baseRing p`, a bijection of $J_H(M)$ with the sections of $g$ over the generic point compatible with addition, Galois action and Hecke operators, and the geometric conditions that $g$ be smooth, separated, locally of finite type, quasi-compact and surjective with preconnected fibres, that $L$ be commutative, and that multiplication by each $n > 0$ for $L$ be flat and surjective. Let $m$ be a natural number with $m > 0$. Then the endomorphism `schemeNsmul m` of the base change of $G$ along $\sigma_A$, i.e. multiplication by $m$ for the relative group law $O.L.baseChange \Lambda.\sigma_A$ over $A$, is locally quasi-finite, quasi-compact and flat.
--
--   This records the basic finiteness and flatness properties of the multiplication-by-$m$ map on the Néron object for $J_H(M)$ after base change to the valuation ring $A$ at the place above $p$, the level-$\Gamma_H(M)$ analogue of the corresponding statement for the level-$\Gamma_0$ object. It is used in the comparison of the generic and special fibres of the Néron object, for instance by [`ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq`](thm.html#ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq) and in the identification of points of $\mathrm{Pic}^0$ of the special fibre with sections through `ptsSp`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m) :
    LocallyQuasiFinite ((O.L.baseChange Λ.σA).schemeNsmul m) ∧
      QuasiCompact ((O.L.baseChange Λ.σA).schemeNsmul m) ∧ Flat ((O.L.baseChange Λ.σA).schemeNsmul m) := by sorry
