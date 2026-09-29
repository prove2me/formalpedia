-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_w_inv_placeOfPoint_eq
-- name    : ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_placeOfPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/1cc8e9d4-23bd-5014-8cb0-329188df5084
-- title:
--   Atkin–Lehner translate of a section: other component, diamond-twisted place
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ and $M/p$ nonzero, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field of the full modular group over $\mathbb{Q}$; let $\mathfrak{X}$ be a bundle `XHDRModelAtP p M H hpM hj` of data and properties for the model `X p (ΓM M H) hj` over $\operatorname{Spec}(R p)$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : R p \to A$ be the ring map inducing the structure map to $\overline{\mathbb{Q}}$. Assume `hdia0`: for every unit $e$ of $\mathbb{Z}/(M/p)$ and every closed point $P$ of the curve model $\mathfrak{X}.\mathrm{Mfib}$, transporting $P$ through $\mathfrak{X}.\mathrm{efib}$, the fibre map of $\mathfrak{X}.\mathrm{dia0}\,e$ and the inverse of $\mathfrak{X}.\mathrm{efib}$ yields a closed point whose place is the translate of the place of $P$ by the semilinear automorphism attached to `diamondActionModL` over the residue field of $A$ at level $M/p$ for the image subgroup `infSubgroup p M H hpM`, evaluated at [`CuspForm.gammaLift (M / p) e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ reducing to $p$, let $i \in \{0,1\}$, let $u$ be a morphism $\operatorname{Spec} A \to$ `X p (ΓM M H) hj` over $\operatorname{Spec}\rho$ whose image lies in $\mathfrak{X}.\mathrm{smoothLocus}$, let $u_\kappa$ be a section of the fibre of `toBase p (ΓM M H) hj` along the residue map composed with $\rho$ which reduces $u$ (that is, $u_\kappa$ followed by the first projection is $\operatorname{Spec}$ of the residue map followed by $u$, and $u_\kappa$ followed by the second projection is the identity), and let $P$ be a closed point of $\mathfrak{X}.\mathrm{Mfib}$ mapping under $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component morphism $\mathfrak{X}.\mathrm{comp}\;i$ to the image of the closed point of the residue field under $u_\kappa$. Then there is a morphism $u'$ over $\operatorname{Spec}\rho$ with $u' = u$ followed by $\mathfrak{X}.w^{-1}$, with image in $\mathfrak{X}.\mathrm{smoothLocus}$, and a section $u'_\kappa$ of the same fibre reducing $u'$ in the same two senses, such that $u'_\kappa$ followed by the fibre map induced by $\mathfrak{X}.w$ is $u_\kappa$, and there is a closed point $P'$ of $\mathfrak{X}.\mathrm{Mfib}$ lying over the image of the closed point under $u'_\kappa$ via $\mathfrak{X}.\mathrm{efib}$ followed by the component morphism with index $1$ if $i = 0$ and $0$ otherwise, whose place equals the translate of the place of $P$ by the semilinear automorphism attached to `diamondActionModL` at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) when $i = 0$, and equals the place of $P$ when $i \neq 0$.
--
--   This records the special-fibre behaviour of the Atkin–Lehner translate of an $A$-valued section of the Deligne–Rapoport model of $X_H(M)$ over $\mathbb{Z}_{(p)}$ at $p \mid M$: translating by $w^{-1}$ moves the reduction to the other of the two components of the special fibre, twisting the associated place by the diamond operator attached to the class of $p$ when passing from the component of index $0$ to that of index $1$. It is used in the comparison of degree-zero pull-backs along $\pi$ and along $\pi \circ w$ in [`ModularCurve.XHDRModelAtP.toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq`](thm.html#ModularCurve.XHDRModelAtP.toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_w_inv_placeOfPoint_eq.lean

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

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_placeOfPoint_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((XHDRLevel.fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (i : Fin 2)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    ∃ (u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      u'.1 = u.1 ≫ 𝔛.w.inv ∧
      Set.range u'.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        uκ' ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w 𝔛.w_over)
          ((IsLocalRing.residue ↥A).comp ρ) = uκ ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ (if i = 0 then 1 else 0)).base P'.1 =
            uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          (𝔛.Mfib A hA ρ hρ).placeOfPoint P' =
            (if i = 0 then (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
              (CuspForm.gammaLift (M / p) pb))) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P
              else (𝔛.Mfib A hA ρ hρ).placeOfPoint P) := by sorry
