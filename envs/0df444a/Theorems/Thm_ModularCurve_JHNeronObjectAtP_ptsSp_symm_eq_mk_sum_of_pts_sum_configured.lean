-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_mk_sum_of_pts_sum_configured
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_mk_sum_of_pts_sum_configured
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/ecab117d-6105-5c23-a48b-a9845d6be6df
-- title:
--   Reduction of bidegree-(0,0) divisors of configured points
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$, the hypothesis $hj$ that `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, and a model datum $\mathfrak X :$ `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $p$ is a nonunit, with residue field $\kappa$ algebraically closed of characteristic $p$; let $\Lambda$ be level data at $A$ and $O$ the associated object `JHNeronObjectAtP p M H hpM A hA Λ`, with structural map $O.g$, generic point identification $O.\mathrm{pts}$ and special identification $O.\mathrm{ptsSp}$ of the glued Picard group `GluedPic0 O.ssFinset` with sections of $O.g$ over `resPt A ≫ Λ.σA`. Let $\rho : R_p \to A$ satisfy $\iota_A \circ \rho =$ the structural map $R_p \to \overline{\mathbb Q}$, and assume $\Lambda.\sigma_A = \mathrm{Spec}\,\rho$. Call a configured point over a component index $c \in \{0,1\}$ a quadruple $(y,u,u_\kappa,P)$: a section $y$ of $\mathfrak X.\mathrm{Meta}.\mathrm{toBase}$, a section $u$ of `toBase p (ΓM M H) hj` over $\mathrm{Spec}\,\rho$ whose base change along $A \hookrightarrow \overline{\mathbb Q}$ is $y$ followed by $\mathfrak X.\mathrm{eeta}$ and the first projection and whose image lies in $\mathfrak X.\mathrm{smoothLocus}$, a $\kappa$-point $u_\kappa$ of the fibre over $\mathrm{residue}\circ\rho$ with $u_\kappa$ followed by the first projection equal to $\mathrm{Spec}(\mathrm{residue})$ followed by $u$ and $u_\kappa$ followed by the second projection the identity, and a closed point $P$ of $(\mathfrak X.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under $\mathfrak X.\mathrm{efib}$ followed by the $c$-th component map $\mathfrak X.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,c$ is the image of the closed point of $\kappa$ under $u_\kappa$. The hypothesis `hsp` is the two-point case: for each $c$, any two configured points over $c$, any degree-zero divisor $D_v$ on $\mathfrak X.\mathrm{Meta}$ equal to $[\,\mathrm{place}(y_1)\,]-[\,\mathrm{place}(y_2)\,]$ and any admissible gluing datum $x$ (first component $[\,\mathrm{place}(P_1)\,]-[\,\mathrm{place}(P_2)\,]$ if $c=0$ and $0$ otherwise, second component the same difference if $c=1$ and $0$ otherwise, third component $0$), there is a section $s$ of $O.g$ over $\Lambda.\sigma_A$ with $O.\mathrm{pts}[D_v]$ equal to $\mathrm{barPt}\,A$ followed by $s$, and with $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ along $\mathrm{resPt}\,A$ equal to the glued class of $x$. Given then $k \in \mathbb N$, component labels $c : \mathrm{Fin}\,k \to \mathrm{Fin}\,2$, configured points $(y_i,u_i,u_{\kappa,i},P_i)$ over $c_i$, integers $n_i$ with $\sum_{c_i=0} n_i = \sum_{c_i=1} n_i = 0$, a degree-zero divisor $D_v = \sum_i n_i\,[\,\mathrm{place}(y_i)\,]$, and an admissible gluing datum $x$ with first component $\sum_{c_i=0} n_i\,[\,\mathrm{place}(P_i)\,]$, second component $\sum_{c_i=1} n_i\,[\,\mathrm{place}(P_i)\,]$ and third component $0$, the conclusion is that a section $s$ of $O.g$ over $\Lambda.\sigma_A$ with $O.\mathrm{pts}[D_v] = \mathrm{barPt}\,A$ followed by $s$ exists, and that every such $s$ satisfies $O.\mathrm{ptsSp}^{-1}$ of its restriction along $\mathrm{resPt}\,A$ equal to the glued class of $x$.
--
--   This is the multi-point form of the reduction dictionary for the Néron object at level $\Gamma_H(M)$ with $p \parallel M$: a divisor class supported on configured points of bidegree $(0,0)$ across the two components of the special fibre extends to an $A$-section, and the reduction of that section is the glued Picard class of the componentwise reductions with trivial datum at the crossings. It is obtained from the two-point case, which enters as a hypothesis, and is used in [`ModularCurve.JHNeronObjectAtP.exists_section_toPic0Pair_eq_mk_of_mem_finPts_of_forall_dvd_ord_tauFree`](thm.html#ModularCurve.JHNeronObjectAtP.exists_section_toPic0Pair_eq_mk_of_mem_finPts_of_forall_dvd_ord_tauFree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_mk_sum_of_pts_sum_configured.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_mk_sum_of_pts_sum_configured
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (k : ℕ) (c : Fin k → Fin 2)
    (y : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : Fin k → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : ∀ i, barPt A ≫ (u i).1 = (y i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (husm : ∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Fin k → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (huκ₁ : ∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (u i).1)
    (huκ₂ : ∀ i, uκ i ≫ pullback.snd _ _ = 𝟙 _)
    (P : Fin k → closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : ∀ i, (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ (c i)).base (P i).1 = (uκ i).base (IsLocalRing.closedPoint (ResidueField ↥A)))

    (n : Fin k → ℤ)
    (hn₀ : ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i = 0)
    (hn₁ : ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i = 0)

    (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (y i)) 1)
    (x : ↥(GluingData.admissible O.ssFinset))
    (hx₁ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
      ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i • Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P i)) 1)
    (hx₂ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
      ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i • Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P i)) 1)
    (hx₃ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0) :
    (∃ s : SchemeHomOver Λ.σA O.g, (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1) ∧
    ∀ s : SchemeHomOver Λ.σA O.g, (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 →
      O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x := by sorry
