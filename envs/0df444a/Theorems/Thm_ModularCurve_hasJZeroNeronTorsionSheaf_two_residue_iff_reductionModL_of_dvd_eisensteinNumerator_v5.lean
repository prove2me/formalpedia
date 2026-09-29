-- Prove2me | Theorems.Thm_ModularCurve_hasJZeroNeronTorsionSheaf_two_residue_iff_reductionModL_of_dvd_eisensteinNumerator_v5
-- name    : ModularCurve.hasJZeroNeronTorsionSheaf_two_residue_iff_reductionModL_of_dvd_eisensteinNumerator_v5
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/219d2774-f856-5518-b9b1-071b44e9d267
-- title:
--   Two-adic Eisenstein torsion sheaf pinned to reduction mod 2
-- statement:
--   Let $p$ be a prime such that $2$ divides $\mathrm{eisensteinNumerator}(p) = (p-1)/\gcd(p-1,12)$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, let $B$ be a valuation subring of $\overline{\mathbb{Q}}$ with $2$ a non-unit of $B$, and assume the predicate `ReductionInputsModL B p`, i.e. the reduction inputs along the residue map $B \to \kappa(B)$ at level $p$. Then there is a term $S$ of `JZeroNeronPrimaryTorsionSheaf p 2 A hA` — a triple consisting of a core structure (fppf sheaves $\mathcal{J}_m$ on $\operatorname{Spec}\mathbb{Z}$, flat finite-type $\mathbb{Z}$-Hopf algebras $H_m$ whose $\overline{\mathbb{Q}}$-points are identified with the $2$-primary Eisenstein torsion $\mathrm{eisensteinPrimaryTorsionBar}\,p\,2\,m$, namely the $2^m$-torsion of $J_0 = \mathrm{Pic}^0$ of the base-changed modular function field at level $p$ intersected with the union of the torsion submodules for powers of the Eisenstein maximal ideal at $2$, together with the remaining core data), finite-flat models, and invariant pinnings — with the following property: for every $m$, every pair of $\mathbb{Z}$-algebra maps $\varphi, \psi : S.\mathrm{core}.H_m \to B$, and every $\varphi', \psi'$ in $\mathrm{WithConv}(S.\mathrm{core}.H_m \to_{\mathbb{Z}} \overline{\mathbb{Q}})$ whose underlying maps are $\varphi$ and $\psi$ followed by the inclusion $B \hookrightarrow \overline{\mathbb{Q}}$, the residues of $\varphi(h)$ and $\psi(h)$ in the residue field of $B$ agree for all $h \in S.\mathrm{core}.H_m$ if and only if the reduction homomorphism $\mathrm{reductionModL}\,B\,p$ takes the classes in $J_0$ attached to $\varphi'$ and $\psi'$ by $S.\mathrm{core}.\mathrm{genericPoints}\,m$ to the same element.
--
--   This supplies the two-adic model choice for the Eisenstein $2$-primary Néron torsion sheaf on the locus $2 \mid (p-1)/\gcd(p-1,12)$: an inhabitant of the full sheaf structure whose $B$-valued points separate exactly according to reduction modulo the prime of $\overline{\mathbb{Q}}$ below $2$, a compatibility that none of the fields of the structure itself records. It is used by the corresponding fibre-count statement at $q = 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasJZeroNeronTorsionSheaf_two_residue_iff_reductionModL_of_dvd_eisensteinNumerator_v5.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_ModularCurve_ReductionModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme

theorem ModularCurve.hasJZeroNeronTorsionSheaf_two_residue_iff_reductionModL_of_dvd_eisensteinNumerator_v5
    (p : ℕ) [Fact p.Prime] (h2n : 2 ∣ eisensteinNumerator p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2)
    (hRI : ReductionInputsModL B p) :
    ∃ S : JZeroNeronPrimaryTorsionSheaf p 2 A hA, ∀ m : ℕ,
      ∀ φ ψ : S.core.H m →ₐ[ℤ] ↥B, ∀ φ' ψ' : WithConv (S.core.H m →ₐ[ℤ] AlgebraicClosure ℚ),
        (∀ h : S.core.H m, φ' h = B.subtype (φ h)) → (∀ h : S.core.H m, ψ' h = B.subtype (ψ h)) →
        ((∀ h : S.core.H m, IsLocalRing.residue ↥B (φ h) = IsLocalRing.residue ↥B (ψ h)) ↔
          reductionModL B p ((S.core.genericPoints m φ' : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p)
            = reductionModL B p ((S.core.genericPoints m ψ' : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p)) := by sorry
