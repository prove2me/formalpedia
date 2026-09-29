-- Prove2me | Theorems.Thm_M4aHerbrand_map_prInf_eq_zero_of_pow_smul_eq_zero
-- name    : M4aHerbrand.map_prInf_eq_zero_of_pow_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/8d2dad93-398e-5f4e-95e9-667ea305af50
-- title:
--   Archimedean local components of p-primary degree-2 classes vanish
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an algebra over $E$ and $F/E$ Galois, and suppose the Galois group $F \simeq_{\mathrm{alg}[E]} F$ acts multiplicatively and distributively on the unit group $(\mathbb{A}_F)^\times$ of the adele ring of $F$, so that this unit group becomes a $\mathbb{Z}$-linear representation of the Galois group. Let $\mathrm{prInf}$ assign to each infinite place $v$ of $F$ a morphism of representations of the decomposition group $D_v$ — the stabiliser of $v$ for the Galois action on infinite places — from the restriction of the adelic unit representation along $D_v \hookrightarrow \mathrm{Gal}(F/E)$ to the representation of $D_v$ on the units $(F_v)^\times$ of the completion of $F$ at $v$. Let $p$ be a prime, and assume that if $p = 2$ then every element of every decomposition group $D_v$ at an infinite place $v$ is trivial. Let $x$ be a class in $H^2(\mathrm{Gal}(F/E), (\mathbb{A}_F)^\times)$ annihilated by $p^k$ for some natural number $k$, i.e. $(p^k : \mathbb{Z}) \cdot x = 0$. Then for every infinite place $v$ of $F$, the image of $x$ in $H^2(D_v, (F_v)^\times)$ under the map induced by the inclusion $D_v \hookrightarrow \mathrm{Gal}(F/E)$ together with $\mathrm{prInf}\,v$ is zero.
--
--   This is the archimedean half of the local-vanishing input to the injectivity of the map from $H^2$ of the idele class (here idele unit) representation to the product of its local components for $p$-primary classes: at an infinite place the decomposition group has order $1$ or $2$, so its degree-$2$ cohomology is killed by $2$, which is coprime to $p^k$ unless $p = 2$, a case excluded by the hypothesis that archimedean decomposition groups are trivial. It is used in [`NumberField.LevelArith.injective_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.injective_of_isBrauerLocalInv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_prInf_eq_zero_of_pow_smul_eq_zero.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem M4aHerbrand.map_prInf_eq_zero_of_pow_smul_eq_zero
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]

    (prInf : ∀ v : InfinitePlace F,
      Rep.res (NumberField.InfPlaceDecomp.decomp E F v).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ NumberField.InfPlaceDecomp.localUnits E F v)
    (p : ℕ) [Fact p.Prime]
    (hinf2 : p = 2 → ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2) (k : ℕ) (hxk : (p ^ k : ℤ) • x = 0)
    (v : InfinitePlace F) :
    (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F v).subtype (prInf v) 2).hom x = 0 := by sorry
