-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul_of_qExpansion_slash
-- name    : ModularCurve.ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul_of_qExpansion_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/53a5af96-37aa-531d-84a1-a85731681e4e
-- title:
--   Pull-back along α sends pt(τ) to pt(α⁻¹τ)
-- statement:
--   Let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup containing $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$, and let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ equal to [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield generated over $\mathbb{Q}$ by the quotients $\overline{p_f}/\overline{p_g}$ of the Laurent series attached to integral power series $p_f, p_g \in \mathbb{Z}[[q]]$ that are the period-one $q$-expansions of two modular forms of a common weight on $\Gamma$, with $\overline{p_g} \ne 0$. Let $D$ be a complex place dictionary for $(\Gamma, F_0)$, i.e. a map $\mathrm{pt}$ from the upper half plane to the places of $\mathbb{C}F_0 =$ [`ModularCurve.laurentBaseChange ℂ F₀`](def/ModularCurve_LaurentCoeff.html#L103) (the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image of $F_0$) together with positive ramification indices, such that $\mathrm{pt}$ is $\Gamma$-invariant, the valuation subring of $\mathrm{pt}(\tau)$ consists of those $x$ whose level-$\Gamma$ realization $z \mapsto$ `realizeOf Γ x z` is bounded in norm on a punctured neighbourhood of $\tau$, and the meromorphic order of that realization at $\tau$ is the ramification index times $\mathrm{ord}_{\mathrm{pt}(\tau)}(x)$. Let $\alpha \in \mathrm{GL}_2(\mathbb{R})$ have positive determinant and satisfy $\alpha T \alpha^{-1} \in \Gamma$ (inside $\mathrm{GL}_2(\mathbb{R})$), and let $\sigma$ be a $\mathbb{C}$-algebra automorphism of $\mathbb{C}F_0$ with the property that for every weight $k$, every pair of modular forms $f, g$ of weight $k$ on $\Gamma$ with integral $q$-expansion power series $p_f, p_g$ (so $p_f, p_g$ map to `qExpansion 1 f`, `qExpansion 1 g`) and $\overline{p_g} \ne 0$, and every $y \in \mathbb{C}F_0$ whose underlying Laurent series is the image of $\overline{p_f}/\overline{p_g}$ in $\mathbb{C}((q))$, one has $\sigma(y) \cdot \widetilde{g\!\mid_k\!\alpha} = \widetilde{f\!\mid_k\!\alpha}$ in $\mathbb{C}((q))$, where $\widetilde{\ \cdot\ }$ denotes the period-one $q$-expansion. Then for every $\tau$ in the upper half plane, the semilinear automorphism $(\sigma, \mathrm{id}_{\mathbb{C}})$ determined by $\sigma$ carries the place $\mathrm{pt}(\tau)$ to $\mathrm{pt}(\alpha^{-1}\tau)$.
--
--   This records how the automorphisms of a modular curve induced by elements of $\mathrm{GL}_2^{+}(\mathbb{R})$ act on non-cuspidal complex points when read on the $q$-expansion function field: pulling functions back along $\tau \mapsto \alpha\tau$ pushes the associated places forward along $\tau \mapsto \alpha^{-1}\tau$. It is used in the construction of the Hecke-equivariant identification of the degree-zero divisor class group of the modular curve with the quotient of a complex vector space by a period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul_of_qExpansion_slash.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul_of_qExpansion_slash
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀)
    (α : GL (Fin 2) ℝ) (hα : 0 < (α.det : ℝ))
    (hTα : α * (ModularGroup.T : GL (Fin 2) ℝ) * α⁻¹ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)))
    (σ : ↥(ModularCurve.laurentBaseChange ℂ F₀) ≃ₐ[ℂ] ↥(ModularCurve.laurentBaseChange ℂ F₀))
    (hσ : ∀ (k : ℤ) (f g : ModularForm Γ k) (pf pg : PowerSeries ℤ),
        ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg →
        ModularCurve.intSeriesC ℚ pg ≠ 0 →
        ∀ y : ↥(ModularCurve.laurentBaseChange ℂ F₀),
          (y : LaurentSeries ℂ) =
            ModularCurve.coeffEmb ℂ (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ((σ y : ↥(ModularCurve.laurentBaseChange ℂ F₀)) : LaurentSeries ℂ) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] α)) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] α)))
    (τ : UpperHalfPlane) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (α⁻¹ • τ) := by sorry
