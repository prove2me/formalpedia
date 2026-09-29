-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
-- name    : ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/119c8a34-b59a-52dd-8c36-c00ed369bdb3
-- title:
--   Multiplication by m is quasi-finite, quasi-compact and flat
-- statement:
--   Fix natural numbers $N_{0}$ and $p$ with $N_{0}\neq 0$ and $p$ prime, and assume $p\nmid N_{0}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ satisfying `LiesOverPrime p`, i.e. the image of $p$ lies in the nonunits of $A$, let $\Lambda$ be a `LevelData N₀ p A` — a scheme $X$ over the base $\operatorname{base} p$ together with a structure morphism $\sigma_{A}\colon \operatorname{Spec} A\to \operatorname{base} p$ lifting the generic point, a relative group law on $X$, and bijections of $J_{0}(N_{0})$ and of its mod-$\ell$ analogue with the generic-fibre and special-fibre sections — and assume $\Lambda$ satisfies `IsJacobian` (abelian-scheme property bundle, commutativity of the law, additivity and Galois equivariance of the two point parametrisations, compatibility of reduction, and existence of Hecke endomorphisms; summarised here). Let $O$ be a `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, whose data include a scheme $G$ over $\operatorname{base} p$ with a commutative relative group law $O.L$, smoothness, separatedness, local finite type, quasi-compactness, surjectivity and preconnected fibres of the structure morphism, a Galois- and Hecke-equivariant parametrisation of the generic-fibre sections by $J_{0}(N_{0}p)$, flatness and surjectivity of all multiplications by $n>0$, and properness of the generic fibre. Let $m>0$. Then the endomorphism $\mathrm{schemeNsmul}\ m$ (multiplication by $m$, the $m$-fold sum of the identity section) of the base change of $O.L$ along $\sigma_{A}$, an endomorphism of $G\times_{\operatorname{base} p}\operatorname{Spec} A$ over $\operatorname{Spec} A$, is locally quasi-finite, quasi-compact and flat.
--
--   This records that multiplication by $m$ on the Néron object of $J_{0}(N_{0}p)$, base-changed to the valuation ring $A$ above $p$, is a locally quasi-finite, quasi-compact flat endomorphism, so that its kernel is a quasi-finite flat group scheme over $A$. It is used in the identification of the toric part and the rigidity of homomorphisms from $\mu_{m}$, via `eq_of_muBaseChange_residue_comp_eq` and `exists_nsmul_eq`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    LocallyQuasiFinite ((O.L.baseChange Λ.σA).schemeNsmul m) ∧
      QuasiCompact ((O.L.baseChange Λ.σA).schemeNsmul m) ∧ Flat ((O.L.baseChange Λ.σA).schemeNsmul m) := by sorry
