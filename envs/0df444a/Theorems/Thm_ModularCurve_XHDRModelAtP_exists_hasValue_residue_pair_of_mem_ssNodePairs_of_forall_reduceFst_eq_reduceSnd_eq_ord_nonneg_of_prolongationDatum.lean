-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/492c3cda-63cc-57f7-a8bc-c84b5e20b9ab
-- title:
--   Common value at supersingular nodes of the reduced fibre
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ in $(\mathbb{Z}/(M/p))^\times$, the hypothesis that $j$ lies in the $q$-expansion function field $\mathrm{qExpFunctionFieldC}\ \mathbb{Q}$ of the full modular group, and a Deligne–Rapoport model datum $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ whose underlying element is $p$, and let $\delta$ be the self-map of the set of places of $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` over $\kappa$ given by the action of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at a $\Gamma_0(M/p)$-lift of $pb$. Let $SS$ be a finite set of pairs of places of $\bar F$ whose members are exactly the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. the pairs $s$ with $s_2$ a supersingular place and $s_1$ its image under the mod-$\ell$ Frobenius place map. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M =$ `xHFunctionFieldBar M H` which, by hypothesis, implements the involution $w$ of the model on places: whenever two $\overline{\mathbb{Q}}$-sections $y, y'$ of $\mathfrak{X}.\mathrm{Meta}$ satisfy that $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first projection and $\mathfrak{X}.w.\mathrm{hom}$ agrees with $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, the associated places satisfy $\mathrm{pointEquivPlace}\ y' = \theta \cdot \mathrm{pointEquivPlace}\ y$. Let $\alpha : F_{M/p} \to F_M$ be a $\overline{\mathbb{Q}}$-algebra homomorphism between the corresponding function fields at level $M/p$ with subgroup `infSubgroup p M H hpM` and at level $M$, with $\alpha$ and $\theta \circ \alpha$ integral and $\alpha$ the identity on underlying Laurent series. Let $Psp$ be a place-specialisation datum `JHPlaceSpecialization p M H hpM A`, with reductions $\mathrm{reduceFst}\ V = Psp.\mathrm{sp}(V|_\alpha)$ and $\mathrm{reduceSnd}\ V = \delta(Psp.\mathrm{sp}(V|_{\theta \circ \alpha}))$, and let $Rpd$ be a prolongation datum for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue maps into $\bar F$, the second obtained from the first by $\theta$. Assume the compatibility $hcomp$: for $i \in \{0,1\}$, any $\overline{\mathbb{Q}}$-section $y$, any lift $u$ of it over $\mathrm{Spec}\,\rho$, any $\kappa$-section $u\kappa$ of the fibre reducing $u$, and any closed point $P_0$ of the fibre curve model $\mathfrak{X}.\mathrm{Mfib}$ lying over the image of the closed point under the $i$-th component map, the place of $P_0$ equals $\mathrm{reduceFst}(\mathrm{pointEquivPlace}\ y)$ for $i = 0$ and $\mathrm{reduceSnd}(\mathrm{pointEquivPlace}\ y)$ otherwise. Then for every $f \in F_M$ lying in the valuation subrings of both $R_1$ and $R_2$ and every pair $s \in SS$: if $0 \le \mathrm{ord}_V(f)$ for every place $V$ of $F_M$ over $\overline{\mathbb{Q}}$ with $\mathrm{reduceFst}\ V = s_1$ and $\mathrm{reduceSnd}\ V = s_2$, then there is $c \in \kappa$ such that the residue $R_1$-reduction of $f$ lies in the valuation ring of $s_1$ with residue the image of $c$, and likewise the $R_2$-reduction of $f$ takes the value $c$ at $s_2$.
--
--   This is the value-matching (algebraic Hartogs) step for the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$: a function integral along both branches through a supersingular node and without horizontal pole at the node has a single well-defined value there, the same on the two components $\Sigma^\infty$ and $\Sigma^0$. It is the form of the gluing statement used further on to produce glued differentials on the reduced fibre and to bound orders of residues, in the analysis of level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)) :
    ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers), ∀ s ∈ SS,
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        Psp.reduceFst α hα V = s.1 → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = s.2 → 0 ≤ V.ord f) →
      ∃ c : ResidueField ↥A,
        s.1.HasValue (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c ∧
        s.2.HasValue (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c := by sorry
