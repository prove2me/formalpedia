-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_Hypothesis79_zetaImage_cross_eq_zero_of_conjIndex
-- name    : OddOrder.Peterfalvi.S09.Hypothesis79.zetaImage_cross_eq_zero_of_conjIndex
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:22:12.671198+00:00
-- url     : https://prove2.me/theorems/39adb338-a467-4a1e-9480-f842da59716c
-- title:
--   Peterfalvi (7.9): cross-orthogonality of the coherent images of distinguished characters
-- statement:
--   Let $G$ be a finite group and `H79 : Hypothesis79 G A₁ L₁ A₂ L₂` a Peterfalvi (7.9) datum: two (7.8) coherence setups (`H79.first`, `H79.second`) over the odd-order group $G$ with disjoint Dade supports. For $m=1,2$ let $\zeta_m$ be the distinguished character `hyp76.zeta zetaDistinct` of the $m$-th setup, and suppose:
--
--   - $\tau_m$ is an integral character map on $L_m$, coherent on the $m$-th source set (`IsCoherent τ_m sourceSet A'_m`), and the setup's $\nu_m$ equals the resulting coherent extension;
--   - $\zeta_m$ is an irreducible character, $\zeta_m\neq\overline{\zeta_m}$, and there is an index $j_m\ne$ `ind1H` of the $m$-th family with $\zeta_{j_m}=\overline{\zeta_m}$;
--   - the class functions `firstZetaImage − ν₁(ζ_{j₁})` and `secondZetaImage − ν₂(ζ_{j₂})` have supports contained in the respective Dade supports `dadeSupport`.
--
--   Then the images `firstZetaImage` and `secondZetaImage` of the distinguished characters are orthogonal:
--   $$\big\langle \text{firstZetaImage},\ \text{secondZetaImage}\big\rangle=0 .$$
--
--   This is the isometry half of the cross-orthogonality step in Peterfalvi (7.9); the support hypotheses are discharged elsewhere from the Dade-agreement property.
--
--   **Formalization Note.** The `Fintype`/`Invertible` instances on $G,L_1,L_2$ are explicit hypotheses in Lean.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusCrossOrtho.lean#L103-L170

import Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis79
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace Hypothesis79

variable {G : Type*} [Group G] [Fintype G]

variable {A₁ : Set G} {L₁ : Subgroup G} [Fintype L₁] [Invertible (Nat.card L₁ : ℂ)]

variable {A₂ : Set G} {L₂ : Subgroup G} [Fintype L₂]

variable [Invertible (Nat.card L₂ : ℂ)] [Invertible (Nat.card G : ℂ)]

theorem zetaImage_cross_eq_zero_of_conjIndex (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁} {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    {A_prime₂ : Set L₂} {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hz₁irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hz₂irr : IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    {j₁ : Fin (H79.first.hyp76.n + 1)} (hj₁ne_ind : j₁ ≠ H79.first.ind1H)
    (hj₁ : H79.first.hyp76.zeta j₁
        = (H79.first.hyp76.zeta H79.first.zetaDistinct).conj)
    (hζ₁ne_conj : H79.first.hyp76.zeta H79.first.zetaDistinct
        ≠ (H79.first.hyp76.zeta H79.first.zetaDistinct).conj)
    {j₂ : Fin (H79.second.hyp76.n + 1)} (hj₂ne_ind : j₂ ≠ H79.second.ind1H)
    (hj₂ : H79.second.hyp76.zeta j₂
        = (H79.second.hyp76.zeta H79.second.zetaDistinct).conj)
    (hζ₂ne_conj : H79.second.hyp76.zeta H79.second.zetaDistinct
        ≠ (H79.second.hyp76.zeta H79.second.zetaDistinct).conj)
    (hab_supp :
      (H79.firstZetaImage - H79.first.nu (H79.first.hyp76.zeta j₁)).support
        ⊆ H79.first.hyp76.hyp71.hyp.dadeSupport)
    (hcd_supp :
      (H79.secondZetaImage - H79.second.nu (H79.second.hyp76.zeta j₂)).support
        ⊆ H79.second.hyp76.hyp71.hyp.dadeSupport) :
    ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0 := by sorry

end Hypothesis79

end OddOrder.Peterfalvi.S09
