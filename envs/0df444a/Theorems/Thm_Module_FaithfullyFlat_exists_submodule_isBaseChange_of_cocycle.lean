-- Prove2me | Theorems.Thm_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle
-- name    : Module.FaithfullyFlat.exists_submodule_isBaseChange_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/495f9b9b-ec5e-5ad5-b88a-aab6dcdb149a
-- title:
--   Effective faithfully flat descent for modules
-- statement:
--   Let $A \to B$ be a homomorphism of commutative rings (in a fixed universe) making $B$ a faithfully flat $A$-module, and let $N$ be an additive group carrying compatible $B$- and $A$-module structures, the $A$-action being the restriction of the $B$-action along $A \to B$. Write $(i_1 A B).\mathrm{hom}$ and $(i_2 A B).\mathrm{hom}$ for the two ring maps $B \to B \otimes_A B$ used throughout `Algebra.DescentCofaces`, whose composites with $A \to B$ agree. Assume given an isomorphism $\varphi'$ in $\mathrm{ModuleCat}(B \otimes_A B)$ between the extensions of scalars of $N$ along these two maps, and assume $\varphi'.\mathrm{hom}$ satisfies the cocycle condition `Cocycle`: the transports $T$ of $\varphi'.\mathrm{hom}$ along the cofaces `c₁₂ A B` and `c₂₃ A B`, composed in that order, equal the transport along `c₁₃ A B`. Then there is an $A$-submodule $M \subseteq N$ with the following four properties. First, $n \in M$ holds exactly when $\varphi'.\mathrm{hom}(1 \otimes_B n) = 1 \otimes_B n$, where $1 \in B \otimes_A B$ and the two sides live in the respective extensions of scalars. Second, `IsBaseChange B M.subtype`: the inclusion $M \hookrightarrow N$ exhibits $N$ as the base change $B \otimes_A M$. Third, there is an isomorphism $\theta : B \otimes_A M \xrightarrow{\sim} N$ in $\mathrm{ModuleCat}(B)$ (the source being the extension of scalars of $M$ along $A \to B$) with $\theta(b \otimes_A m) = b \cdot m$ for all $b \in B$, $m \in M$, and such that the extension of $\theta.\mathrm{hom}$ along $(i_1 A B).\mathrm{hom}$ followed by $\varphi'.\mathrm{hom}$ equals `canonical A B (ModuleCat.of A M)` followed by the extension of $\theta.\mathrm{hom}$ along $(i_2 A B).\mathrm{hom}$; here `canonical` is the comparison built from the two `ModuleCat.extendScalarsComp` isomorphisms and the equality of the composite ring maps $A \to B \to B \otimes_A B$. Fourth, if $N$ is an invertible $B$-module then $M$ is an invertible $A$-module. No unit or diagonal normalisation of $\varphi'$ is assumed.
--
--   This is effective descent for modules along a faithfully flat ring homomorphism (Grothendieck's descent theorem, Amitsur's theorem in the commutative case), phrased entirely in terms of `ModuleCat.extendScalars` so that a descent datum arising on the scheme side can be fed in without further translation; the extra clause on invertibility rests on [`Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat`](thm.html#Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat). It is used in the construction of a descent datum isomorphism for invertible modules on an affine scheme along a flat surjective affine morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle.lean

import Mathlib
import Definitions.Def_Algebra_DescentCofaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open TensorProduct CategoryTheory Algebra.DescentCofaces

theorem Module.FaithfullyFlat.exists_submodule_isBaseChange_of_cocycle
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of B N) ≅
      (ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of B N))
    (hcocycle : Cocycle (ModuleCat.of B N) φ'.hom) :
    ∃ M : Submodule A N,
      (∀ n : N, n ∈ M ↔
        φ'.hom (((1 : B ⊗[A] B) ⊗ₜ[B] n : (ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of B N))) =
          ((1 : B ⊗[A] B) ⊗ₜ[B] n : (ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of B N))) ∧
      IsBaseChange B M.subtype ∧
      (∃ θ : (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M) ≅ ModuleCat.of B N,
        (∀ (b : B) (m : M),
          θ.hom ((b ⊗ₜ[A] m : (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M))) = b • (m : N)) ∧
        (ModuleCat.extendScalars (i₁ A B).hom).map θ.hom ≫ φ'.hom =
          canonical A B (ModuleCat.of A M) ≫ (ModuleCat.extendScalars (i₂ A B).hom).map θ.hom) ∧
      (Module.Invertible B N → Module.Invertible A M) := by sorry
