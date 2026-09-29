-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre
-- name    : ModularCurve.JHNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/1b1832e5-8cce-55ec-a838-ba4587681969
-- title:
--   fppf-local sections of m-torsion over the abelian-quotient square
-- statement:
--   Fix a natural number $M \neq 0$ and a prime $p$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ such that $p$ is a non-unit of $A$ (`A.LiesOverPrime p`) and whose residue field $\kappa$ is algebraically closed of characteristic $p$. Let $\Lambda$ be level data for $(p, M, H, A)$, that is: a morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` compatible with the generic point, a scheme $X$ with structure morphism $f \colon X \to$ `base p`, a relative group law $\Lambda.L$ on $f$ over `baseRing p`, and bijections identifying the generic-fibre and residue-fibre points of $f$ with $J_H(M/p)$-type and $\operatorname{Pic}^0$-type groups; assume $f$ proper. Let $O$ be a `JHNeronObjectAtP` for these data, with relative group law $O.L$ on $g \colon G \to$ `base p`, and let $m > 0$. All schemes below are the base changes along $\operatorname{Spec}\kappa \to \operatorname{Spec} A \to$ `base p`; for a relative group law, `schemeKer m` denotes the fibre product of the $m$-fold multiplication morphism `schemeNsmul m` with the unit section, and `schemeKerStr m` its projection to the base. Suppose given $\psi$ from the $m$-torsion scheme of $O.L$ over $\kappa$ to the fibre product over $\kappa$ of the $m$-torsion scheme of $\Lambda.L$ with itself, such that composing $\psi$ with the first (respectively second) projection and then with the inclusion of the $m$-torsion into the ambient scheme equals the inclusion of the $m$-torsion of $O.L$ followed by the underlying morphism of `O.abqFibre 0` (respectively `O.abqFibre 1`). Then there exist a scheme $U$, a flat, surjective, locally of finite presentation morphism $u$ from $U$ to that fibre product of $m$-torsion schemes, and a morphism $s \colon U \to$ ($m$-torsion of $O.L$ over $\kappa$) with $\psi \circ s = u$.
--
--   This is the fppf-local surjectivity of the map from the $m$-torsion of the special fibre of the Néron-type object to the square of the $m$-torsion of the abelian quotient: the map admits a section after a faithfully flat, finitely presented cover. It is used, together with the identification of the kernel pair with a split torus, in the computation of the order of the special-fibre $m$-torsion in [`ModularCurve.JHNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq`](thm.html#ModularCurve.JHNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP AlgebraicCurve
open scoped TensorProduct

theorem ModularCurve.JHNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (hΛ : IsProper Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m)
    (ψ : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶
      pullback ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m))
    (hψ₀ : ψ ≫ pullback.fst _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 0).1)
    (hψ₁ : ψ ≫ pullback.snd _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 1).1) :
    ∃ (U : Scheme.{0}) (u : U ⟶ pullback ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m))
      (_ : Flat u) (_ : Surjective u) (_ : LocallyOfFinitePresentation u)
      (s : U ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m), s ≫ ψ = u := by sorry
