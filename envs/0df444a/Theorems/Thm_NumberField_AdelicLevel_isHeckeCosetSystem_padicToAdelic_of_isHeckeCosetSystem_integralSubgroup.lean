-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup
-- name    : NumberField.AdelicLevel.isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/4d99c75f-7f2d-5e28-b002-1edb4b7ea071
-- title:
--   Local-to-adelic transfer of Hecke coset systems away from the level
-- statement:
--   Let $N$ be a nonzero natural number and $\ell$ a prime not dividing $N$, let $\iota$ be an index type and let $\alpha : \iota \to \mathrm{GL}_2(\mathbb{Q}_\ell)$. Assume $\alpha$ is a Hecke coset system, in the sense of [`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15), for the subgroup [`LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ]`](def/LocalLanglands_LocalHeckeInstance.html#L13) — the image of $\mathrm{GL}_2(\mathbb{Z}_\ell)$ under the entrywise map induced by $\mathbb{Z}_\ell \to \mathbb{Q}_\ell$ — and the element [`HeckeIntegralSeam.padicDiagP ℓ`](def/LocalLanglands_PadicHeckeCosetSystem.html#L23), namely the invertible matrix $\mathrm{diag}(\ell, 1)$ over $\mathbb{Q}_\ell$: each $\alpha i$ lies in the double coset $\mathrm{GL}_2(\mathbb{Z}_\ell)\,\mathrm{diag}(\ell,1)\,\mathrm{GL}_2(\mathbb{Z}_\ell)$, every element of that double coset has the same image as some $\alpha i$ in $\mathrm{GL}_2(\mathbb{Q}_\ell)/\mathrm{GL}_2(\mathbb{Z}_\ell)$, and $i \mapsto \alpha i\,\mathrm{GL}_2(\mathbb{Z}_\ell)$ is injective. The conclusion is that the family $i \mapsto$ [`AdelicDock.padicToAdelic ℓ (α i)`](def/AdelicDock_LocalEmbedding.html#L254), obtained by placing $\alpha i$ at the height-one prime [`AdelicDock.padicPlace ℓ`](def/AdelicDock_LocalEmbedding.html#L231) of $\mathcal{O}_\mathbb{Q}$ attached to $\ell$, embedding into $\mathrm{GL}_2$ of the finite adeles of $\mathbb{Q}$ and then into $\mathrm{GL}_2$ of the full adele ring, is again a Hecke coset system, now for the subgroup which is the intersection of [`NumberField.AdelicLevel.levelOne`](def/NumberField_AdelicLevel.html#L589) at the ideal [`AdelicDock.ratLevel N`](def/AdelicDock_LocalEmbedding.html#L303) $= (N)$ — the preimage under the finite-part homomorphism `glFin` of the finite-adelic level-one congruence subgroup `finiteLevelOne` of level $(N)$ — with [`AutomorphicForm.finiteAdelicGL2Subgroup ℚ`](def/AutomorphicForm_SmoothAutomorphicFnAt.html#L15), the kernel of the archimedean-component map `glArch`, and for the element [`NumberField.AdelicLevel.heckeGen`](def/NumberField_AdelicLevel.html#L800) at the place [`AdelicDock.padicPlace ℓ`](def/AdelicDock_LocalEmbedding.html#L231), the Hecke generator built from the uniformizer unit at that place. Thus the three conditions (membership in the adelic double coset, covering of its left cosets, injectivity on left cosets) hold for the transported family.
--
--   This is the standard comparison between the local Hecke coset decomposition of $\mathrm{GL}_2(\mathbb{Z}_\ell)\,\mathrm{diag}(\ell,1)\,\mathrm{GL}_2(\mathbb{Z}_\ell)$ and the adelic double coset of the Hecke generator at $\ell$ for a level group of level $N$ with $\ell \nmid N$: away from the level, the adelic double coset is governed by its component at $\ell$. It is used in the comparison of the adelic Hecke action with the $q$-expansion coefficients of a cusp form, via [`CuspForm.IsAdelicLiftOf.sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem`](thm.html#CuspForm.IsAdelicLiftOf.sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup.lean

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_PadicHeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.AdelicLevel.isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup
    {N : ℕ} (hN : N ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    {ι : Type*} (α : ι → GL (Fin 2) ℚ_[ℓ])
    (hα : HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ])
      (HeckeIntegralSeam.padicDiagP ℓ) α) :
    HeckeIntegralSeam.IsHeckeCosetSystem
      (NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N) ⊓
        AutomorphicForm.finiteAdelicGL2Subgroup ℚ)
      (NumberField.AdelicLevel.heckeGen (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace ℓ))
      (fun i => AdelicDock.padicToAdelic ℓ (α i)) := by sorry
