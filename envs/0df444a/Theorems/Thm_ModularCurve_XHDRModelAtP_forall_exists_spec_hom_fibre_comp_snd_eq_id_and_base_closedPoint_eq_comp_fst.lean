-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_spec_hom_fibre_comp_snd_eq_id_and_base_closedPoint_eq_comp_fst
-- name    : ModularCurve.XHDRModelAtP.forall_exists_spec_hom_fibre_comp_snd_eq_id_and_base_closedPoint_eq_comp_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/18f8d38a-3ee8-5c20-b475-0dc72cae2bae
-- title:
--   Crossings of the special fibre are κ_A-rational points
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and the standing hypothesis `hj` that the Laurent series `jqModC ℚ` (the $q$-expansion $q^{-1}\cdot$`jNum` of $j$) lies in `qExpFunctionFieldC ℚ ⊤`, the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios of integral forms of level $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over `R p`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`A.LiesOverPrime p`) whose residue field $\kappa_A$ is algebraically closed of characteristic $p$, and let $\rho :$ `R p` $\to A$ be a ring map whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Write $X_{\kappa_A} =$ `fibre ((IsLocalRing.residue ↥A).comp ρ)` for the base change of the model `X p (ΓM M H) hj` along `R p` $\to A \to \kappa_A$, and let `𝔛.comp A hA ρ hρ 0`, `𝔛.comp A hA ρ hρ 1` be the two component morphisms of $\mathfrak{X}$ into $X_{\kappa_A}$. Then for every point $n$ of the fibre product of these two morphisms there is a morphism $t : \operatorname{Spec} \kappa_A \to X_{\kappa_A}$ with $t$ followed by the projection `pullback.snd` equal to the identity of $\operatorname{Spec}\kappa_A$, and such that $t$ sends the closed point of $\kappa_A$ to the image under `𝔛.comp A hA ρ hρ 0` of the first projection of $n$.
--
--   The statement says that every intersection point of the two components of the geometric special fibre of the Deligne–Rapoport type model of $X_H(M)$ at $p$ (with $p$ exactly dividing $M$) is a $\kappa_A$-rational point, cut out by an honest section of the structure morphism over $\operatorname{Spec}\kappa_A$. It supplies the rationality input for the construction of charts around a crossing and for the identification of the crossing points, being used in [`ModularCurve.XHDRModelAtP.exists_prime_tensorProduct_chartAlgFin_crossing_and_section_closes`](thm.html#ModularCurve.XHDRModelAtP.exists_prime_tensorProduct_chartAlgFin_crossing_and_section_closes), [`ModularCurve.XHDRModelAtP.forall_exists_orientedCrossingChart_valuationSubring`](thm.html#ModularCurve.XHDRModelAtP.forall_exists_orientedCrossingChart_valuationSubring) and [`ModularCurve.XHDRModelAtP.forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective`](thm.html#ModularCurve.XHDRModelAtP.forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_forall_exists_spec_hom_fibre_comp_snd_eq_id_and_base_closedPoint_eq_comp_fst.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.forall_exists_spec_hom_fibre_comp_snd_eq_id_and_base_closedPoint_eq_comp_fst
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      ∃ t : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) =
          (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) := by sorry
