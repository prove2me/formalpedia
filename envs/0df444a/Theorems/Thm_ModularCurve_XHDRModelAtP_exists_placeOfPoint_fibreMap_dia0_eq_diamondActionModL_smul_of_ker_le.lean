-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
-- name    : ModularCurve.XHDRModelAtP.exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/6d13493a-093c-5e9a-a781-c3c0fa2040f2
-- title:
--   Diamond ⟨ e⟩ on places of the mod-p dictionary model
-- statement:
--   Fix a natural number $p$ that is prime and a nonzero level $M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and assume $p \mid M$ but $p^{2} \nmid M$, that every unit of $\mathbb{Z}/M$ whose image under the reduction map $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is $1$ lies in $H$, and that $M/p \neq 0$. Assume $j$, in its $q$-expansion form `jqModC ℚ`, lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios at full level, and let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which packages the integral models of $X_H(M)$ and of the auxiliary level $\Gamma_N$ over the base ring `R p` (properness, flatness, integrality, normality on affine opens, relative smoothness of dimension one at the auxiliary level), a curve model `Meta` over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` together with its identification `eeta` with the generic fibre, Galois equivariance of its points, the chart pinning conditions, and the diamond data including the automorphisms $\mathrm{dia}_0$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p \in A.\mathrm{nonunits}$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : \mathrm{R}\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $\mathrm{R}\,p \to \overline{\mathbb{Q}}$. Then for every $e \in (\mathbb{Z}/(M/p))^{\times}$ and every closed point $P$ of the curve underlying the dictionary model $\mathfrak{X}.\mathrm{Mfib}\,A\,\rho$ of the special fibre, the point obtained by transporting $P$ through the base map of `𝔛.efib`, then through the base map of the fibre map over the residue homomorphism $(\mathrm{residue}\,A) \circ \rho$ induced by the isomorphism $\mathfrak{X}.\mathrm{dia}_0\,e$ viewed as a morphism over the base, and then back through the base map of the inverse of `𝔛.efib`, is again a closed point, and its place equals the place of $P$ translated by the element of the semilinear automorphism group $\mathrm{SemilinearAut}$ attached, via $\sigma \mapsto (\sigma, 1)$, to the algebra automorphism `diamondActionModL` over the residue field of $A$ at level $M/p$ with subgroup the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, evaluated at a chosen lift [`CuspForm.gammaLift (M / p) e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $e$ to $\Gamma_0(M/p)$.
--
--   This is the statement that the special fibre of the diamond automorphism $\langle e\rangle$ of the Deligne–Rapoport integral model, read in the dictionary presentation of the fibre at a place above $p$, acts on places of the function field by the characteristic-$p$ diamond automorphism `diamondActionModL`; the hypothesis $p^{2} \nmid M$ ensures $M/p$ is invertible in the residue field, so that this is the genuine diamond. It supplies the diamond compatibility used in assembling the level data for the relative Picard dictionary of the Jacobian Néron object at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by sorry
