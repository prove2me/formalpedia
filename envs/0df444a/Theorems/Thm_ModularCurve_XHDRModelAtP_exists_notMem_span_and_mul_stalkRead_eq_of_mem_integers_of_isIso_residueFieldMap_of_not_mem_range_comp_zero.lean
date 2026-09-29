-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_zero
-- name    : ModularCurve.XHDRModelAtP.exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/c7ec7919-02a6-574a-af32-37b139b5a0b7
-- title:
--   Clearing denominators outside the vertical prime at a non-crossing point
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$ and $p^2\nmid M$, a subgroup $H\le(\mathbb Z/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p\mid M$ is $1$, with $M/p\neq 0$, and assume $j$ lies in the $q$-expansion function field of the full level, so that the Deligne–Rapoport type package $\mathfrak X$ of level $\Gamma_M$ over $R\,p$ is available. Let $A\subseteq\overline{\mathbb Q}$ be a valuation subring with $p$ a non-unit, residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho:R\,p\to A$ a ring map inducing the structure map to $\overline{\mathbb Q}$; let $\theta$ be a $\overline{\mathbb Q}$-algebra automorphism of $F=$ `xHFunctionFieldBar M H`, `Psp` a place specialisation datum for $(p,M,H,A)$ and `Rpd` a prolongation datum for it and $\theta$, so that `Rpd.R₂` is a valuation subring of $F$ with residue map onto the special-fibre function field; the hypothesis `hwgen` says that two $\overline{\mathbb Q}$-points of $\mathfrak X$`.Meta.C` over the base whose images under $\mathfrak X$`.eeta`, the first projection and $\mathfrak X$`.w.hom` agree have places differing by the semilinear automorphism `SemilinearAut.ofAlgAut` $\theta$. Further let $O'$ be a discrete valuation domain with uniformiser $\varpi'$, $\rho_{O'}:R\,p\to O'$, an injective local homomorphism $\iota_{A'}:O'\to A$ with $\iota_{A'}\circ\rho_{O'}=\rho$, and $j_{O'}:O'\to\overline{\mathbb Q}$ compatible with these, and let $u_\kappa$ be a section of the geometric special fibre over $\kappa$ (so $u_\kappa$ followed by the second projection is the identity) whose closed point avoids the image of $\mathfrak X$`.comp A hA ρ hρ 0`. Put $x'$ for the image of that closed point in $X_{O'}=$ `XO (ΓM M H) hj ρO'` under the base-change map `bcMap`, $B=\mathcal O_{X_{O'},x'}$, and $\sigma_B:O'\to B$ the structural map obtained from the global sections of `XO.toBase`. Assume the residue field map of `XO.toBase` at $x'$ is an isomorphism, and let `hsp` witness that the image of the generic point of $\mathfrak X$`.Meta.C` under $\mathfrak X$`.eeta` followed by the projection $pr_{J'}$ to $X_{O'}$ induced by $j_{O'}$ specialises to $x'$; let $\mathrm{emb}:B\to F$ be the resulting reading of germs as functions, namely `stalkSpecializes hsp` followed by the stalk maps of $pr_{J'}$ and $\mathfrak X$`.eeta` and the inverse of $\mathfrak X$`.Meta.ffEquiv`. The conclusion: for every $x\in F$ lying in `Rpd.R₂.integers`, if $x\cdot\mathrm{emb}(s_0)=\mathrm{emb}(r_0)$ for some $r_0,s_0\in B$ with $s_0\neq0$, then there are $r,s\in B$ with $s\notin(\sigma_B\varpi')$ and $x\cdot\mathrm{emb}(s)=\mathrm{emb}(r)$.
--
--   This is the Hartogs-type step at a non-crossing point of the special fibre: a function integral for the prolongation `Rpd.R₂` and a priori only a fraction of germs at $x'$ can be written with denominator outside the vertical height-one prime $\sigma_B(\varpi')B$, the localisation of the two-dimensional normal local ring $B$ there being dominated by the prolongation's valuation ring. It feeds [`ModularCurve.XHDRModelAtP.mem_range_stalk_read_of_mem_integers_of_forall_isStrictSnd_mem`](thm.html#ModularCurve.XHDRModelAtP.mem_range_stalk_read_of_mem_integers_of_forall_isStrictSnd_mem), where integrality for the prolongations is converted into membership in the image of the stalk at $x'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_zero
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (ρO' : R p →+* O')
    (ιA' : O' →+* ↥A) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA') (hιA'ρ : ιA'.comp ρO' = ρ)
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ)
    (ϖ' : O') (hϖ' : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'})

    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hsm : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI bc' := bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI x' : ↥(XO (ΓM M H) hj ρO') := bc'.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    letI B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)

    IsIso ((XO.toBase (ΓM M H) hj ρO').residueFieldMap x') →
    ∀ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x'),
    letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom))
    ∀ x : ↥(xHFunctionFieldBar M H), x ∈ Rpd.R₂.integers → (∃ r₀ s₀ : ↥B, s₀ ≠ 0 ∧ x * emb s₀ = emb r₀) →
      ∃ r s : ↥B, s ∉ Ideal.span {σB ϖ'} ∧ x * emb s = emb r := by sorry
