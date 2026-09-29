-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_isFinite_schemeKerStr_special_and_finrank_eq_natCard_torsion
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.isFinite_schemeKerStr_special_and_finrank_eq_natCard_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/a8d99fb9-c970-5e7c-973a-ae8ddd1f61ed
-- title:
--   Finiteness and order of the m-torsion of the special fibre
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $p \mid M$, $H$ a subgroup of $(\mathbb{Z}/M)^{\times}$, and $A$ a valuation subring of $\overline{\mathbb{Q}}$; write $R$ for the subring of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$, $\kappa$ for the residue field of $A$, and $H'$ for the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$ under reduction. Let $\Lambda$ be level data at $A$: a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} R$ whose composite with $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec} A$ is the canonical $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec} R$, a scheme $X$ with a morphism $f \colon X \to \operatorname{Spec} R$, a relative group law $L$ on $f$ (multiplication, unit and inverse on $T$-points over $\operatorname{Spec} R$, natural in $T$), a bijection $\mathrm{pts}$ from $J_{H'}(M/p) = \mathrm{Pic}^{0}$ of the function field of $X_{H'}(M/p)$ over $\overline{\mathbb{Q}}$ onto the sections of $f$ over $\operatorname{Spec}\overline{\mathbb{Q}}$, and a bijection from $\mathrm{Pic}^{0}$ of the corresponding function field over $\kappa$ onto the sections of $f$ over $\operatorname{Spec}\kappa \to \operatorname{Spec} R$. Assume that $f$ is smooth and proper, has connected fibres and admits a relative group law, and that $\mathrm{pts}$ is additive for $L$. Fix $m > 0$, and let $L_{\kappa}$ be the base change of $L$ along $\operatorname{resPt} A$ followed by $\sigma_A$, a group law on $X \times_{\operatorname{Spec} R} \operatorname{Spec}\kappa \to \operatorname{Spec}\kappa$. Then the structure morphism to $\operatorname{Spec}\kappa$ of the kernel scheme of $m$ for $L_{\kappa}$ — the pullback of the multiplication-by-$m$ endomorphism along the unit section — is a finite morphism, and the $\kappa$-dimension of the global sections of that kernel scheme, taken as a $\kappa$-algebra via its structure morphism, equals the cardinality of the subgroup of elements killed by $m$ in $\mathrm{Pic}^{0}$ of the function field of $X_{H'}(M/p)$ over $\overline{\mathbb{Q}}$.
--
--   This is the order computation for the $m$-torsion group scheme of the special fibre of an abelian scheme with prescribed generic fibre: finite flatness of multiplication by $m$ over the discrete valuation ring $R$, together with reducedness of the geometric generic fibre, lets the rank be read off from the number of $m$-torsion points of $J_{H'}(M/p)$ over $\overline{\mathbb{Q}}$. It feeds the count of toric and finite parts used in building the level-$M$ object at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_isFinite_schemeKerStr_special_and_finrank_eq_natCard_torsion.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP
open AlgebraicCurve

theorem ModularCurve.JHNeronObjectAtP.LevelData.isFinite_schemeKerStr_special_and_finrank_eq_natCard_torsion
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (m : ℕ) (hm : 0 < m) :
    IsFinite ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) =
       Nat.card ↥(Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) m)) := by sorry
