-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/befa1670-61db-5488-bacd-68549a2fdd78
-- title:
--   Reduction mod m of a toric matrix across an isomorphism
-- statement:
--   Fix a natural number $p$ and a valuation subring $A$ of $\overline{\mathbb Q}$, and work over `base p` $=\operatorname{Spec}$ of the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$. Given schemes $G,G_0$ with structure morphisms $g,g_0$ to `base p`, two morphisms $\sigma,\sigma_0\colon\operatorname{Spec}A\to$ `base p` with $\sigma=\sigma_0$, relative group laws $L$ on $g$ and $L_0$ on $g_0$, mutually inverse morphisms $\Psi\colon G\to G_0$ and $\Psi'\colon G_0\to G$ over `base p` (so $\Psi$ followed by $\Psi'$ is $\mathbb 1_G$ and $\Psi'$ followed by $\Psi$ is $\mathbb 1_{G_0}$) such that composition with $\Psi'$ turns the $L_0$-product of any two points of $g_0$ over `barPt A ≫ σ₀` into the $L$-product; further, $m>0$, ranks $t,t_0$, morphisms $\iota_m$ from $\mu$ over $A$ of rank $t$, level $m$ to the base change $g\times_{\text{base}}\operatorname{Spec}A$, and $\iota^0_m$ likewise of rank $t_0$ to the base change of $g_0$, each compatible with products of characters in the sense that composing with the point `muPt` of a product $\chi\chi'$ in `WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ)` gives the base-changed group law applied to the two separate compositions; morphisms $\tau,\tau_0$ from the split tori of ranks $t,t_0$ over the residue field of $A$ to the base changes of $g,g_0$ along `resPt A ≫ σ`, `resPt A ≫ σ₀`, with the reductions of $\iota_m,\iota^0_m$ factoring through $\mu\to\mathbb G_m^{\,\cdot}$ followed by $\tau$, $\tau_0$ (projected to $G$, $G_0$); additive maps $M_0\colon\mathbb Z^{t_0}\to\mathbb Z^{t}$ and $M_0'\colon\mathbb Z^{t}\to\mathbb Z^{t_0}$ whose induced morphisms of tori over the residue field intertwine $\tau,\tau_0$ with $\Psi$ and with $\Psi'$ respectively; and the rigidity hypothesis that two morphisms from $\mu$ of rank $t$, level $m$ over $A$ to the base change of $g$, both compatible with products of characters as above, which agree after restriction along the reduction `muBaseChange (residue ↥A) t m`, are equal. The conclusion: there is an additive map $\bar M\colon(\mathbb Z/m)^{t_0}\to(\mathbb Z/m)^{t}$ whose composition with the coordinatewise reduction $\mathbb Z^{t_0}\to(\mathbb Z/m)^{t_0}$ equals $M_0$ followed by the reduction $\mathbb Z^{t}\to(\mathbb Z/m)^{t}$, and such that for every $A$-algebra homomorphism $\chi\colon A[(\mathbb Z/m)^{t}]\to\overline{\mathbb Q}$ the point `muPt A t m χ` followed by $\iota_m$, the projection to $G$ and $\Psi$ coincides with the point `muPt A t₀ m` of $\chi\circ$ `mapDomainAlgHom ↥A ↥A Mbar` followed by $\iota^0_m$ and the projection to $G_0$.
--
--   This transports the toric matrix of an isomorphism between two group objects over $\mathbb Z_{(p)}$ from the torus in the special fibre to the $m$-torsion multiplicative subgroups over the valuation ring, the transport being pinned down by rigidity of multiplicative lifts. It is used in the comparison of the finite and toric points of the Néron objects attached to $J_H$ at $p$, via [`ModularCurve.map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge`](thm.html#ModularCurve.map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid
    {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {G G₀ : Scheme.{0}} {g : G ⟶ base p} {g₀ : G₀ ⟶ base p}
    (σ σ₀ : Spec (CommRingCat.of ↥A) ⟶ base p) (hσ : σ = σ₀)
    (L : RelativeGroupLaw (baseRing p) g) (L₀ : RelativeGroupLaw (baseRing p) g₀)
    (Ψ : SchemeHomOver g g₀) (Ψ' : SchemeHomOver g₀ g) (hΨΨ' : Ψ.1 ≫ Ψ'.1 = 𝟙 G) (hΨ'Ψ : Ψ'.1 ≫ Ψ.1 = 𝟙 G₀)
    (hΨ'mul : ∀ x y : SchemeHomOver (barPt A ≫ σ₀) g₀, NeronModelInfra.schemeHomOverComp (L₀.mul _ x y) Ψ' =
      L.mul _ (NeronModelInfra.schemeHomOverComp x Ψ') (NeronModelInfra.schemeHomOverComp y Ψ'))
    {t t₀ : ℕ} (m : ℕ) (hm : 0 < m)
    (ιm : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (ι₀m : SchemeHomOver (muStr ↥A t₀ m) (RelativeGroupLaw.baseChangeStr σ₀ g₀))
    (hιm_mul : ∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) ιm =
        (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) ιm)
          (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) ιm))
    (hι₀m_mul : ∀ χ χ' : WithConv (muCoord ↥A t₀ m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A t₀ m (χ * χ').ofConv) ι₀m =
        (L₀.baseChange σ₀).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t₀ m χ.ofConv) ι₀m)
          (NeronModelInfra.schemeHomOverComp (muPt A t₀ m χ'.ofConv) ι₀m))
    (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (τ₀ : SchemeHomOver (torusStr (ResidueField ↥A) t₀) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ₀) g₀))
    (hιm_sp : muBaseChange (residue ↥A) t m ≫ ιm.1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (hι₀m_sp : muBaseChange (residue ↥A) t₀ m ≫ ι₀m.1 ≫ pullback.fst g₀ σ₀ =
      muToTorus (ResidueField ↥A) t₀ m ≫ τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ₀))
    (M₀ : (Fin t₀ → ℤ) →+ (Fin t → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ τ₀.1 ≫
        pullback.fst g₀ (resPt A ≫ σ₀) = τ.1 ≫ pullback.fst g (resPt A ≫ σ) ≫ Ψ.1)
    (M₀' : (Fin t → ℤ) →+ (Fin t₀ → ℤ))
    (hM₀' : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀')) ≫ τ.1 ≫
        pullback.fst g (resPt A ≫ σ) = τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ₀) ≫ Ψ'.1)
    (RIGID : ∀ u v : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g),
      (∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
        NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) u =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) u)
            (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) u)) →
      (∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
        NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) v =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) v)
            (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) v)) →
      muBaseChange (residue ↥A) t m ≫ u.1 = muBaseChange (residue ↥A) t m ≫ v.1 → u = v) :
    ∃ Mbar : (Fin t₀ → ZMod m) →+ (Fin t → ZMod m),
      Mbar.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t₀ => ℤ) i)) =
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)).comp M₀ ∧
      ∀ χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ,
        (muPt A t m χ).1 ≫ ιm.1 ≫ pullback.fst g σ ≫ Ψ.1 =
          (muPt A t₀ m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).1 ≫ ι₀m.1 ≫ pullback.fst g₀ σ₀ := by sorry
