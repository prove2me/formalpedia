-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion
-- name    : ModularCurve.JZeroNeronObjectAtP.schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/9c5c925d-437d-5932-a32f-403d23aac049
-- title:
--   Multiplicativity on torsion torus points of the special fibre
-- statement:
--   Fix a natural number $p$ and write $\mathcal{O} =$ `baseRing p` for the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $p$, with base scheme $\operatorname{Spec}\mathcal{O}$; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with residue field $\kappa =$ `ResidueField ↥A`, and let $\sigma \colon \operatorname{Spec} A \to \operatorname{Spec}\mathcal{O}$ be a morphism. Let $g \colon G \to \operatorname{Spec}\mathcal{O}$ and $g_0 \colon G_0 \to \operatorname{Spec}\mathcal{O}$ be separated, each carrying two relative group laws over $\mathcal{O}$, namely $L, L^c$ for $g$ and $L_0, L^c_0$ for $g_0$ (a relative group law assigns to every $T \to \operatorname{Spec}\mathcal{O}$ a group structure on the set of $T$-points of the structure morphism, functorially in $T$). Let $\Psi$ be a morphism $G \to G_0$ over $\operatorname{Spec}\mathcal{O}$ which is a homomorphism from $L^c$ to $L^c_0$ on $T$-points for every $T \to \operatorname{Spec}\mathcal{O}$; assume moreover that $L$ and $L^c$ agree on points over $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec} A \xrightarrow{\sigma} \operatorname{Spec}\mathcal{O}$, and likewise $L_0$ and $L^c_0$. Fix $t \in \mathbb{N}$ and a morphism $\tau$ from the split torus $\operatorname{Spec}\kappa[\mathbb{Z}^t]$ to the fibre $G \times_{\operatorname{Spec}\mathcal{O}} \operatorname{Spec}\kappa$ over $\operatorname{Spec}\kappa$, together with, for each $m > 0$, a morphism $\iota_m$ from $\operatorname{Spec}A[(\mathbb{Z}/m)^t]$ to $G \times_{\operatorname{Spec}\mathcal{O}} \operatorname{Spec}A$ over $\operatorname{Spec}A$, such that the composite of $\iota_m$ with the reduction $\operatorname{Spec}\kappa[(\mathbb{Z}/m)^t] \to \operatorname{Spec}A[(\mathbb{Z}/m)^t]$ and the projection to $G$ equals the composite $\operatorname{Spec}\kappa[(\mathbb{Z}/m)^t] \to \operatorname{Spec}\kappa[\mathbb{Z}^t] \xrightarrow{\tau} G_\kappa \to G$. Finally let $\chi, \chi' \colon \kappa[\mathbb{Z}^t] \to \kappa$ be $\kappa$-algebra homomorphisms which are torsion, in the sense that for each of them there is $n \in \mathbb{N}$ with $n \neq 0$ in $\kappa$ and $\chi(\mathrm{single}\,v\,1)^n = 1$ for all $v \in \mathbb{Z}^t$. Then the base change $\Psi_\kappa$ of $\Psi$ along $\operatorname{Spec}\kappa \to \operatorname{Spec}A \xrightarrow{\sigma} \operatorname{Spec}\mathcal{O}$ carries the $L$-product (base-changed to $\kappa$, at the identity point of $\operatorname{Spec}\kappa$) of the two $\kappa$-points $\tau \circ \chi$ and $\tau \circ \chi'$ of $G_\kappa$ to the corresponding $L_0$-product of their images: $\Psi_\kappa(\tau(\chi) \cdot_L \tau(\chi')) = \Psi_\kappa(\tau(\chi)) \cdot_{L_0} \Psi_\kappa(\tau(\chi'))$.
--
--   This transfers multiplicativity of $\Psi$ from the auxiliary laws $L^c, L^c_0$, for which it holds on all points, to the structure laws $L, L_0$ on the torsion points of a split torus inside the special fibre, the point being that such points lift to $A$-points through the multiplicative subschemes $\iota_m$. It is used in the comparison of Hecke-equivariant maps on the toric parts of the Néron models of the Jacobians $J_0$ at $p$, in [`ModularCurve.map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge`](thm.html#ModularCurve.map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion
    {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {G G₀ : Scheme.{0}} {g : G ⟶ base p} {g₀ : G₀ ⟶ base p}
    (σ : Spec (CommRingCat.of ↥A) ⟶ base p) [IsSeparated g] [IsSeparated g₀]
    (L Lc : RelativeGroupLaw (baseRing p) g) (L₀ Lc₀ : RelativeGroupLaw (baseRing p) g₀) (Ψ : SchemeHomOver g g₀)
    (hΨc : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (Lc.mul s x y) Ψ =
        Lc₀.mul s (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))
    (hL : ∀ a b : SchemeHomOver (barPt A ≫ σ) g, L.mul _ a b = Lc.mul _ a b)
    (hL₀ : ∀ a b : SchemeHomOver (barPt A ≫ σ) g₀, L₀.mul _ a b = Lc₀.mul _ a b)
    {t : ℕ} (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (ιm : ∀ m : ℕ, 0 < m → SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (hιm_sp : ∀ (m : ℕ) (hm : 0 < m), muBaseChange (residue ↥A) t m ≫ (ιm m hm).1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (χ χ' : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A)
    (hχ : ∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ (AddMonoidAlgebra.single v 1) ^ n = 1)
    (hχ' : ∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ' (AddMonoidAlgebra.single v 1) ^ n = 1) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange (resPt A ≫ σ)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ))
        (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ) =
      (L₀.baseChange (resPt A ≫ σ)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ))
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ) (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ)) := by sorry
