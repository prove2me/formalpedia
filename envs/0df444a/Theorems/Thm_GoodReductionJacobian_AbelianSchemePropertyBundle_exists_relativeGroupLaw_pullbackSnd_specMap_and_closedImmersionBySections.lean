-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_relativeGroupLaw_pullbackSnd_specMap_and_closedImmersionBySections
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_relativeGroupLaw_pullbackSnd_specMap_and_closedImmersionBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/51cb7f17-04a1-51fd-95da-2d1efab0d8d0
-- title:
--   Base change to a field of an abelian scheme with sections presentation
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism. Assume given: a relative group law $L$ for $f$, i.e. for every scheme $T$ with a morphism $t : T \to \operatorname{Spec} S$ a multiplication, unit and inversion on the set of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$ satisfying associativity, the unit laws and left inversion, and compatible with composition along any $\psi : T' \to T$ over $\operatorname{Spec} S$; the bundle `AbelianSchemePropertyBundle` for $f$, i.e. $f$ is smooth, proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law; a module $\mathcal L$ on $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit module of $U$; and the hypothesis `ClosedImmersionBySections` for $\mathcal L$ and $f$, i.e. for some $N$ there is a `ProjPresentation`: sections $\sigma_0,\dots,\sigma_N$ of $\mathcal L$ over $A$ together with a morphism $A \to \mathbb{P}^N_S$ over $\operatorname{Spec} S$ which trivialises $\mathcal L$ via $\sigma_i$ on the preimage of the standard chart $X_i \ne 0$ and matches the coordinate ratios, and whose structure morphism to $\mathbb{P}^N_S$ is a closed immersion. Let $K$ be a field with an $S$-algebra structure, and write $A_K$ for the chosen pullback of $f$ along $\operatorname{Spec} K \to \operatorname{Spec} S$, with projections $p_1 : A_K \to A$ and $f_K : A_K \to \operatorname{Spec} K$. Then there exists a relative group law on $f_K$ such that `AbelianSchemePropertyBundle` holds for $f_K$, the pullback $p_1^{*}\mathcal L$ is invertible, and `ClosedImmersionBySections` holds for $p_1^{*}\mathcal L$ and $f_K$.
--
--   This is the base-change statement along a field-valued point for the package of data used for the Jacobian of a modular curve: the abelian-scheme properties, the relative group law, and an invertible module together with a projective presentation by global sections realising a closed immersion into $\mathbb{P}^N$. It is used in the study of the fibres of such a family over a field, in particular by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_forall_subsingleton_HSucc_pullback_fst_of_closedImmersionBySections`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_forall_subsingleton_HSucc_pullback_fst_of_closedImmersionBySections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_relativeGroupLaw_pullbackSnd_specMap_and_closedImmersionBySections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_relativeGroupLaw_pullbackSnd_specMap_and_closedImmersionBySections
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    (K : Type) [Field K] [Algebra S K] :
    ∃ L' : RelativeGroupLaw K (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)),
      AbelianSchemePropertyBundle K (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)) ∧
      Scheme.Modules.IsInvertible
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap S K))).obj 𝓛) ∧
      Scheme.Modules.ClosedImmersionBySections
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap S K))).obj 𝓛)
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)) := by sorry
