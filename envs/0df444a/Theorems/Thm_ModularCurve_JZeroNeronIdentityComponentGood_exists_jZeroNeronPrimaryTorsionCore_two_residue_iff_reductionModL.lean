-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL
-- name    : ModularCurve.JZeroNeronIdentityComponentGood.exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/b860acbc-eb21-57d8-a7af-45a3560bc593
-- title:
--   Mod-2 residue dictionary for the Eisenstein torsion core
-- statement:
--   Let $p$ be a prime such that $2$ divides $\mathrm{eisensteinNumerator}(p) = (p-1)/\gcd(p-1,12)$, and let $N$ be a record of type `JZeroNeronIdentityComponentGood p`, i.e. a Néron identity component datum for $J_0(p)$ together with good-prime data at every prime $\ell$ not dividing $p$. Let $A$ be a valuation subring of $\overline{\mathbf Q}$ with $p$ lying in its nonunits, and $B$ a valuation subring of $\overline{\mathbf Q}$ with $2$ lying in its nonunits, and assume the reduction inputs `ReductionInputsModL B p`, i.e. the inputs for reduction along the residue map of $B$ for level $p$. The assertion is that there exists a core $C$ of type `JZeroNeronPrimaryTorsionCore p 2 A hA` — in particular a family of fppf sheaves on $\operatorname{Spec}\mathbf Z$ together with flat finite-type $\mathbf Z$-Hopf algebras $C.H_m$ whose $\overline{\mathbf Q}$-points, taken in `WithConv`, are identified by $C.\mathrm{genericPoints}\,m$ with the subgroup $\ker(2^m)\cap\bigcup_k$ (torsion by the $k$-th power of the Eisenstein maximal ideal) of $\mathrm{JZero}\,p = \mathrm{Pic}^0$ of the base-changed modular function field — such that for every $m$, every pair of $\mathbf Z$-algebra maps $\varphi,\psi : C.H_m \to B$ and every pair $\varphi',\psi'$ of elements of `WithConv` $(C.H_m \to_{\mathbf Z} \overline{\mathbf Q})$ whose underlying maps are $\varphi$, respectively $\psi$, followed by the inclusion $B \hookrightarrow \overline{\mathbf Q}$: the maps $\varphi$ and $\psi$ agree after composition with the residue map $B \to B/\mathfrak m_B$ if and only if the reductions `reductionModL B p` of the points of $\mathrm{JZero}\,p$ attached to $\varphi'$ and $\psi'$ by $C.\mathrm{genericPoints}\,m$ coincide in $\mathrm{JZero}$ over the residue field of $B$.
--
--   This produces, from a Néron identity component with good-prime data, the $2$-primary Eisenstein torsion-sheaf core for $J_0(p)$ together with the dictionary identifying congruence of $B$-valued points modulo the maximal ideal of $B$ with equality of their reductions in the Jacobian over $\overline{\mathbf F}_2$, in the style of Mazur's analysis of the Eisenstein ideal. It is the main input to the construction of the full torsion-sheaf record, [`ModularCurve.hasJZeroNeronTorsionSheaf_two_residue_iff_reductionModL_of_dvd_eisensteinNumerator_v5`](thm.html#ModularCurve.hasJZeroNeronTorsionSheaf_two_residue_iff_reductionModL_of_dvd_eisensteinNumerator_v5).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponentGood
import Definitions.Def_ModularCurve_ReductionModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme

theorem ModularCurve.JZeroNeronIdentityComponentGood.exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL
    (p : ℕ) [Fact p.Prime] (h2n : 2 ∣ eisensteinNumerator p)
    (N : JZeroNeronIdentityComponentGood p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2)
    (hRI : ReductionInputsModL B p) :
    ∃ C : JZeroNeronPrimaryTorsionCore p 2 A hA, ∀ m : ℕ,
      ∀ φ ψ : C.H m →ₐ[ℤ] ↥B, ∀ φ' ψ' : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ),
        (∀ h : C.H m, φ' h = B.subtype (φ h)) → (∀ h : C.H m, ψ' h = B.subtype (ψ h)) →
        ((∀ h : C.H m, IsLocalRing.residue ↥B (φ h) = IsLocalRing.residue ↥B (ψ h)) ↔
          reductionModL B p ((C.genericPoints m φ' : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p)
            = reductionModL B p ((C.genericPoints m ψ' : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p)) := by sorry
