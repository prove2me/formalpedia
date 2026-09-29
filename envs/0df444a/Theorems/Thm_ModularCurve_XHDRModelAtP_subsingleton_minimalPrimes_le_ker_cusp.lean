-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_subsingleton_minimalPrimes_le_ker_cusp
-- name    : ModularCurve.XHDRModelAtP.subsingleton_minimalPrimes_le_ker_cusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/296ace1d-957b-5012-9e6d-976b60f3d5d9
-- title:
--   Uniqueness of the fibre component through the cusp at infinity
-- statement:
--   Fix a prime $p$ and $M \ge 1$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a witness $hj$ that the $q$-expansion `jqModC ℚ` (the Laurent series $q^{-1}$ times the power series `jNum` over $\mathbb{Q}$) lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios of integral forms of full level. Let $\mathfrak{P}$ be an element of `XHDRModelAtP p M H hpM hj`, i.e. a bundle of data and properties for the two-chart integral model of $X_H(M)$ over $R_p = \mathbb{Z}$ localised at $p$: properness, flatness, integrality and local finite presentation of the structure morphism to $\operatorname{Spec} R_p$, integral closedness of the sections on affine opens, properness and relative-dimension-one smoothness at the auxiliary level $\Gamma_N$, an identification `Meta` of the base change to $\overline{\mathbb{Q}}$ with a curve model having function field `xHFunctionFieldBar M H`, Galois equivariance of the point–place correspondence, compatibility of the finite chart with $q$-expansions, smoothness and geometric integrality of the generic fibre, and further fields, among them a map `𝔓.rhoInf` from the pole-chart algebra to $R_p$ playing the role of the cusp at infinity. Write $\mathcal{O} =$ `chartAlgInf p (ΓM M H) hj` for the pole chart, the subalgebra of elements of `qExpFunctionFieldC ℚ (ΓM M H)` integral over $R_p[j^{-1}]$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa =$ `IsLocalRing.ResidueField A` is algebraically closed of characteristic $p$; let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map, with $\kappa$ an $R_p$-algebra via the residue map composed with $\rho$. Let $\mathrm{ev} : \kappa \otimes_{R_p} \mathcal{O} \to \kappa$ be a $\kappa$-algebra homomorphism with $\mathrm{ev}(1 \otimes b)$ the image of `𝔓.rhoInf b` in $\kappa$ for every $b \in \mathcal{O}$. Then any two minimal primes $P, P'$ of $\kappa \otimes_{R_p} \mathcal{O}$ that are contained in $\ker(\mathrm{ev})$ coincide.
--
--   In classical terms: the reduced cusp at infinity, viewed on the pole chart of the geometric special fibre of the Deligne–Rapoport model of $X_H(M)$ at $p \mid M$, lies on exactly one irreducible component of that fibre. The statement is used by [`ModularCurve.XHDRModelAtP.mem_range_comp_zero_iff_map_ker_le`](thm.html#ModularCurve.XHDRModelAtP.mem_range_comp_zero_iff_map_ker_le), where the component through the cusp has to be singled out.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_subsingleton_minimalPrimes_le_ker_cusp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

theorem ModularCurve.XHDRModelAtP.subsingleton_minimalPrimes_le_ker_cusp
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) (IsLocalRing.ResidueField ↥A)]
    (halg : algebraMap (R p) (IsLocalRing.ResidueField ↥A) = (IsLocalRing.residue ↥A).comp ρ)
    (ev : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A]
      IsLocalRing.ResidueField ↥A)
    (hev : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      ev (1 ⊗ₜ b) = algebraMap (R p) (IsLocalRing.ResidueField ↥A) (𝔓.rhoInf b)) :
    ∀ (P P' : Ideal ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))),
      P ∈ minimalPrimes ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj)) →
      P' ∈ minimalPrimes ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj)) →
      P ≤ RingHom.ker ev → P' ≤ RingHom.ker ev → P = P' := by sorry
