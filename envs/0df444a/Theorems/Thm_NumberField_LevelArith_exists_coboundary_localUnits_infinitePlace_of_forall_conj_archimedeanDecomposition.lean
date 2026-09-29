-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition
-- name    : NumberField.LevelArith.exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/fcfd161e-53cd-5255-9239-a947b30342cf
-- title:
--   Archimedean local splitting of an S-unit 2-cocycle
-- statement:
--   Let $L\subseteq F$ be intermediate fields of $\overline{\mathbb Q}/\mathbb Q$, both finite over $\mathbb Q$, with $F/\mathbb Q$ normal, and let $F_L$ denote `levelField L F hLF`, namely $F$ with its structure of extension of $L$ obtained by extending scalars, assumed normal over $L$. Let $T$ be a finite set of nonzero primes of $\mathcal O_L$ and let $f$ be a $2$-cocycle of $\mathrm{Gal}(F_L/L)$ with values in the representation [`NumberField.SUnits.sUnitsRep`](def/NumberField_SUnitsModule.html#L52), the subrepresentation of $F_L^{\times}$ (written additively) cut out by the $T$-unit submodule; write $x\mapsto$ `val` for the underlying unit of such a value. Let $v$ be an infinite place of $L$. Write $c$ for the automorphism of $\overline{\mathbb Q}$ induced by complex conjugation through a fixed embedding, and $\langle c\rangle=$ `archimedeanDecomposition` for the subgroup of integral powers of $c$ in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$. Assume: for every $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ such that $\sigma g\sigma^{-1}$ fixes $L$ pointwise for all $g\in\langle c\rangle$, there is $c_1\colon\langle c\rangle\to\overline{\mathbb Q}^{\times}$ with $$f\bigl((\sigma g\sigma^{-1})|_{F_L},(\sigma h\sigma^{-1})|_{F_L}\bigr)=(\sigma g\sigma^{-1})(c_1(h))\cdot c_1(gh)^{-1}\cdot c_1(g)$$ in $\overline{\mathbb Q}^{\times}$, the restriction being `levelGal`. The conclusion: putting $w=$ [`NumberField.ArchIdele.above`](def/NumberField_ArchimedeanIdeleModule.html#L155) $L\,F_L\,v$, the chosen infinite place of $F_L$ above $v$, and $D_w$ for its stabiliser in $\mathrm{Gal}(F_L/L)$ acting on $(F_L)_w^{\times}$, there exists $y\colon D_w\to (F_L)_w^{\times}$ such that for all $a,b\in D_w$ the image of $f(a,b)$ under the canonical map $F_L\to (F_L)_w$ equals $a(y(b))\cdot y(ab)^{-1}\cdot y(a)$.
--
--   This is the archimedean half of the local-splitting input to a computation of the local-global obstruction for $S$-unit classes in degree two: a cocycle which splits on every $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$-conjugate of the archimedean decomposition group lying in $\mathrm{Gal}(\overline{\mathbb Q}/L)$ splits, after completion, on the decomposition group of each infinite place of $L$. It is used in [`groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_archimedean_eq_zero_pPrimary_continuousH2Sr_sUnitsMax`](thm.html#groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_archimedean_eq_zero_pPrimary_continuousH2Sr_sUnitsMax), where the vanishing of all local restrictions forces the vanishing of a global degree-two class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition.lean

import Mathlib
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory IsDedekindDomain NumberField NumberField.LevelArith ExtCitation
open scoped NumberField.LevelArith NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]
    (T : Finset (HeightOneSpectrum (𝓞 ↥L)))
    (f : groupCohomology.cocycles₂ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) T))
    (v : InfinitePlace ↥L)
    (hyp : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (hσ : ∀ g : ↥archimedeanDecomposition,
        σ * (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹ ∈ L.fixingSubgroup),
      ∃ c₁ : ↥archimedeanDecomposition → Additive (AlgebraicClosure ℚ)ˣ, ∀ g h : ↥archimedeanDecomposition,
        Additive.ofMul (Units.map (algebraMap ↥(levelField L F hLF) (AlgebraicClosure ℚ)).toMonoidHom
            (NumberField.SUnits.val ↥L ↥(levelField L F hLF) T
              (f (levelGal L F hLF ⟨σ * (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹, hσ g⟩,
                  levelGal L F hLF ⟨σ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹, hσ h⟩)))) =
          Additive.ofMul ((σ * (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹) • Additive.toMul (c₁ h))
            - c₁ (g * h) + c₁ g) :
    ∃ y : ↥(NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF)
          (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)) →
        NumberField.InfPlaceDecomp.localUnits ↥L ↥(levelField L F hLF) (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v),
      ∀ a b : ↥(NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)),
        Additive.ofMul (Units.map (NumberField.SIdele.locInf ↥L ↥(levelField L F hLF) v).toMonoidHom
            (NumberField.SUnits.val ↥L ↥(levelField L F hLF) T
              (f ((a : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)),
                  (b : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)))))) =
          (NumberField.InfPlaceDecomp.localUnits ↥L ↥(levelField L F hLF)
              (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)).ρ a (y b) - y (a * b) + y a := by sorry
