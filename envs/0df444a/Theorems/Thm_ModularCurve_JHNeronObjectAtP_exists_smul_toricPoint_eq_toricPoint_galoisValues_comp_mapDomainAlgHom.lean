-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
-- name    : ModularCurve.JHNeronObjectAtP.exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/733af50f-96ae-58c2-aab7-cfbe67e23e5f
-- title:
--   Frobenius acting on toric points via the reduced Frobenius matrix
-- statement:
--   Fix a prime $p$ and $M>0$ with $p\mid M$, a subgroup $H\le(\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (`LiesOverPrime`), whose residue field is algebraically closed of characteristic $p$; fix level data $\Lambda$ and an object $O$ of `JHNeronObjectAtP` over it, so that $O$ carries a scheme $G$ with structure morphism $g$ to the base, a relative group law, an identification $O.\mathrm{pts}$ of $J_H(M)$ with sections over the generic point, a toric rank $t=O.\mathrm{toricRank}$, a torus fibre morphism and a toric lift. Assume given an endomorphism $\Xi_G$ of the pullback of $g$ along the residue point $\mathrm{resPt}\,A$ followed by $\Lambda.\sigma_A$ which commutes with the first projection and covers, through the second projection, $\operatorname{Spec}$ of the $p$-power Frobenius of the residue field; and an additive endomorphism $P_0$ of $\mathbb{Z}^{t}$ such that coefficientwise Frobenius on $\mathrm{AddMonoidAlgebra}$ followed by the torus fibre morphism agrees with the exponent map induced by $P_0$ followed by the torus fibre morphism and then $\Xi_G$. Let $\varphi$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ lying in the decomposition subgroup of $A$ and acting on the residue field by $x\mapsto x^{p}$, and let $m>0$. Then there is an additive endomorphism $\bar P$ of $(\mathbb{Z}/m)^{t}$ reducing $P_0$, i.e. commuting with the componentwise reduction map $\mathbb{Z}^{t}\to(\mathbb{Z}/m)^{t}$, such that for every $A$-algebra homomorphism $\chi:\mathrm{AddMonoidAlgebra}\,A\,((\mathbb{Z}/m)^{t})\to A$ there is an $A$-algebra homomorphism $\chi^{\varphi}$ of the same kind with $\chi^{\varphi}(\mathrm{single}\,g\,1)=\varphi\cdot\chi(\mathrm{single}\,g\,1)$ for all $g\in(\mathbb{Z}/m)^{t}$, and with $\varphi$ acting on the toric point of $\chi$ (pushed into $\overline{\mathbb{Q}}$) by sending it to the toric point of $\chi^{\varphi}$ precomposed with the exponent map $\mathrm{mapDomainAlgHom}$ of $\bar P$.
--
--   This is the statement that a Frobenius element of the decomposition group at $A$ acts on the toric points of $J_H(M)$ — the points coming from the multiplicative part of the Néron object at $p$ — by moving character values by $\varphi$ and twisting the character group by the mod $m$ reduction of the Frobenius matrix $P_0$ of the torus fibre. It is the input for the computation, at $m=p^{n}$, of the Galois action on toric points through the cyclotomic character, used for the action of the $U$-operator on toric points and for the corresponding statement about the Tate-style Galois representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)

    (ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA))
    (hΞ₁ : ΞG ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞ₂ : ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)))
    (P₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hP₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) (frobenius (ResidueField ↥A) p))) ≫ O.torusFibre.1 =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) P₀)) ≫ O.torusFibre.1 ≫ ΞG)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)
    (m : ℕ) (hm : 0 < m) :
    ∃ Pbar : (Fin O.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m),
      Pbar.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)) =
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)).comp P₀ ∧
      ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A,
        ∃ χφ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A,
          (∀ g : Fin O.toricRank → ZMod m,
            χφ (AddMonoidAlgebra.single g 1) = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • χ (AddMonoidAlgebra.single g 1)) ∧
          φ • O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χ) =
            O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χφ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Pbar))) := by sorry
