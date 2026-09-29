-- Prove2me | Theorems.Thm_ModularCurve_forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap
-- name    : ModularCurve.forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/2a2a1298-ce99-5d40-b765-53debe7b5fac
-- title:
--   Integrality and residue of γ on Pl⊗ B
-- statement:
--   Fix a prime $p$, a positive integer $M$ with $p \mid M$, and a subgroup $H \le (\mathbb{Z}/M)^{\times}$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $\rho :$ `R p` $\to Pl$ be a ring homomorphism whose composition with the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$ is the structure map of `R p`, and suppose $Pl$ carries an `R p`-algebra structure whose structure map is $\rho$. Let $B$ be an `R p`-subalgebra of the field $\mathrm{qExpFunctionFieldC}\ \mathbb{Q}\ (\Gamma_M(M,H))$ — the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ of integral $q$-expansions of modular forms of equal weight for that group — such that every $b \in B$ is the coefficientwise image, under the structure map `R p` $\to \mathbb{Q}$, of some Laurent series $y$ over `R p`. Let $r_0 : B \to \mathrm{qExpFunctionFieldC}\ (\mathrm{ResidueField}\ Pl)\ (\Gamma_N(p,M,H))$ be a ring homomorphism which, on any such integral lift $y$ of $b$, returns the coefficientwise reduction of $y$ along $\mathrm{residue} \circ \rho$. Let $Rg$ be a regular prolongation of $Pl$ to $\mathrm{xHFunctionFieldBar}(M,H)$, the intermediate field of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of $\mathrm{xHFunctionField}(M,H)$, with residue field $\mathrm{qExpFunctionFieldC}\ (\mathrm{ResidueField}\ Pl)\ (\Gamma_M(M,H))$; that is, a valuation subring $Rg.\mathrm{integers}$ together with a surjective ring map $Rg.\mathrm{residue}$ onto that field with kernel the maximal ideal, inducing the given valuation and residue map on $Pl$, and having the non-degeneracy property that every nonzero element becomes a unit-scaled element with nonzero residue. Assume $Rg$ satisfies the $q$-integrality clause: whenever a Laurent series $y$ over $Pl$ has its image in $\overline{\mathbb{Q}}((q))$ lying in $\mathrm{xHFunctionFieldBar}(M,H)$, that element is $Rg$-integral and its $Rg$-residue is, as a Laurent series over $\mathrm{ResidueField}\ Pl$, the coefficientwise reduction of $y$. Finally let $\gamma : Pl \otimes_{\mathrm{R}\,p} B \to \mathrm{xHFunctionFieldBar}(M,H)$ and $r : Pl \otimes_{\mathrm{R}\,p} B \to \mathrm{qExpFunctionFieldC}\ (\mathrm{ResidueField}\ Pl)\ (\Gamma_N(p,M,H))$ be ring homomorphisms pinned on pure tensors by $\gamma(\alpha \otimes b) = \alpha \cdot b$ (the scalar $\alpha$ acting on the coefficientwise image of the $q$-expansion of $b$) and $r(\alpha \otimes b) = \mathrm{residue}(\alpha)\, r_0(b)$. Then for every $t \in Pl \otimes_{\mathrm{R}\,p} B$ the element $\gamma(t)$ lies in $Rg.\mathrm{integers}$ and its $Rg$-residue equals $r(t)$ as Laurent series over $\mathrm{ResidueField}\ Pl$.
--
--   This is the tensor-level form of the $q$-expansion principle used to read functions on a chart of the modular curve $X_H(M)$ base-changed to a place $Pl$ of $\overline{\mathbb{Q}}$: integrality and reduction of an arbitrary element of $Pl \otimes B$ are computed coefficientwise on the cusp component. It is cited in the computation of the order of a place of the $X_H$ Deligne–Rapoport model at a point, [`ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap`](thm.html#ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups TensorProduct
open IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel

theorem ModularCurve.forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)

    (B : Subalgebra (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hlift : ∀ b : ↥B, ∃ y : LaurentSeries (R p),
      coeffMap (algebraMap (R p) ℚ) y = (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))

    (r₀ : ↥B →+* ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM)))
    (hr₀ : ∀ (b : ↥B) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) →
      ((r₀ b : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)) =
        coeffMap ((residue ↥Pl).comp ρ) y)

    (Rg : RegularProlongation Pl ↥(xHFunctionFieldBar M H) ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H)))
    (hq : ∀ (y : LaurentSeries ↥Pl) (hy : coeffMap Pl.subtype y ∈ xHFunctionFieldBar M H),
      ∃ hO : (⟨coeffMap Pl.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
        ((Rg.residue ⟨_, hO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H))) : LaurentSeries (ResidueField ↥Pl)) =
          coeffMap (residue ↥Pl) y)

    (γ : ↥Pl ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (α : ↥Pl) (b : ↥B), ((γ (α ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (α : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (r : ↥Pl ⊗[R p] ↥B →+* ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM)))
    (hr : ∀ (α : ↥Pl) (b : ↥B), ((r (α ⊗ₜ b) : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)) =
      residue ↥Pl α • ((r₀ b : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)))
    (t : ↥Pl ⊗[R p] ↥B) :
    ∃ hO : γ t ∈ Rg.integers,
      ((Rg.residue ⟨γ t, hO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H))) : LaurentSeries (ResidueField ↥Pl)) =
        ((r t : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)) := by sorry
