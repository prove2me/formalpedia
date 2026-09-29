-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/eb5fc770-7059-5644-907d-6bfe7058782d
-- title:
--   Frobenius action on toric points via a reduced Frobenius matrix
-- statement:
--   Fix $N_0$ and a prime $p$ with $p \nmid N_0$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, level data $\Lambda$ for $(N_0,p,A)$ satisfying `IsJacobian`, and a Néron object $O$ over these data, the residue field of $A$ having characteristic $p$. Let $t = O.\mathrm{toricRank}$. Assume given an endomorphism $\Xi_G$ of the fibre $\mathrm{pullback}\,(O.g)\,(\mathrm{resPt}\,A \gg \Lambda.\sigma_A)$ which commutes with the first projection and whose composite with the second projection is the second projection followed by $\mathrm{Spec}$ of the $p$-power Frobenius of the residue field, and an additive endomorphism $P_0$ of $\mathbb{Z}^t$ such that applying the residue-field Frobenius to the coefficients of $\mathrm{AddMonoidAlgebra}$ over $\mathbb{Z}^t$, followed by $O.\mathrm{torusFibre}$, agrees with reindexing along $P_0$ followed by $O.\mathrm{torusFibre}$ and then $\Xi_G$. Let $\varphi$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ lying in the decomposition subgroup of $A$ and acting on the residue field by $x \mapsto x^p$, and let $m > 0$. Then there is an additive endomorphism $\bar{P}$ of $(\mathbb{Z}/m)^t$ whose composite with componentwise reduction $\mathbb{Z}^t \to (\mathbb{Z}/m)^t$ equals that reduction composed with $P_0$, such that for every $A$-algebra map $\chi : \mathrm{AddMonoidAlgebra}\,A\,((\mathbb{Z}/m)^t) \to A$ there is an $A$-algebra map $\chi^{\varphi}$ of the same source and target with $\chi^{\varphi}(\mathrm{single}\,g\,1) = \varphi \cdot \chi(\mathrm{single}\,g\,1)$ for all $g \in (\mathbb{Z}/m)^t$ (the action of $\varphi$ as element of the decomposition subgroup), and such that in $\mathrm{JZero}\,(N_0 p)$ one has $\varphi \cdot O.\mathrm{toricPoint}\,m\,\chi = O.\mathrm{toricPoint}\,m\,(\chi^{\varphi} \circ \mathrm{mapDomainAlgHom}\,\bar{P})$, both characters being composed with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$.
--
--   This records the Galois action of a Frobenius element at $A$ on the toric points of the Néron object of $J_0(N_0 p)$ at $p$: conjugation by $\varphi$ moves the values of a character of the $m$-torsion of the split torus by $\varphi$ and reindexes them by a mod-$m$ reduction of the Frobenius matrix $P_0$ of the toric part of the special fibre (for $m$ a power of $p$ this is where the cyclotomic character enters). It feeds the identification of the Frobenius and torus matrices and the bridge statement about Frobenius-stability of the toric points together with the action of the Hecke generators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    [CharP (ResidueField ↥A) p]

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
