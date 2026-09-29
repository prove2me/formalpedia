-- Prove2me | Theorems.Thm_NumberField_pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
-- name    : NumberField.pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/4838c1ad-2d4b-5ea8-9914-714100aa17ed
-- title:
--   Base-changed idèles become norms after raising to n'/[F:E]
-- statement:
--   Let $E, F, N, L'$ be number fields equipped with algebra structures $E \to F$, $E \to N$, $F \to N$, $E \to L'$, $L' \to N$ forming scalar towers $E \subseteq F \subseteq N$ and $E \subseteq L' \subseteq N$, with $N/F$ Galois with commutative Galois group and $L'/E$ Galois with commutative Galois group. Assume the homomorphism $\mathrm{Aut}_F(N) \to \mathrm{Aut}_E(L')$ given by restricting scalars to $E$ and then restricting to the normal subextension $L'$ (the map `resHom E L' F N`) is injective. Let $n' \in \mathbb{N}$ be such that $g^{n'} = 1$ for every $g \in \mathrm{Aut}_E(L')$, and assume $\mathrm{finrank}_E F \mid n'$. Then for every unit $u$ of the adèle ring $\mathbb{A}_E$ of $E$, the image of $u$ under the unit-group map induced by the base-change ring homomorphism $\beta$ of `genuineBaseChange E F` (the morphism $\mathbb{A}_E \to \mathbb{A}_F$ compatible with $E \to F$), raised to the power $n'/\mathrm{finrank}_E F$ (natural-number division), lies in the join, inside $\mathbb{A}_F^\times$, of the subgroup `principalIdeles (𝓞 F) F` of idèles coming from $F^\times$ and the range of the idelic norm of `genuineBaseChange F N`, i.e. of the map $\mathbb{A}_N^\times \to \mathbb{A}_F^\times$ induced by the algebra norm of $\mathbb{A}_N$ over $\mathbb{A}_F$.
--
--   This is the arithmetic input of the Artin–Tate construction of the global fundamental class by passage to a compositum with an auxiliary abelian layer: an idèle of $E$, base changed to $F$ and raised to the power $[L':E]/[F:E]$, becomes a principal idèle times a norm from $N$. It is used in [`NumberField.IdeleClassGroup.exists_sum_rho_pow_eq_of_forall_rho_eq`](thm.html#NumberField.IdeleClassGroup.exists_sum_rho_pow_eq_of_forall_rho_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand M4aHerbrand.GenuineDescent LanglandsTunnell.P2.Artin

theorem NumberField.pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
    (E F N L' : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Field N] [NumberField N]
    [Field L'] [NumberField L']
    [Algebra E F] [Algebra E N] [Algebra F N] [Algebra E L'] [Algebra L' N]
    [IsScalarTower E F N] [IsScalarTower E L' N]
    [IsGalois F N] [IsMulCommutative (N ≃ₐ[F] N)] [IsGalois E L'] [IsMulCommutative (L' ≃ₐ[E] L')]
    (hinj : Function.Injective (resHom E L' F N))
    (n' : ℕ) (hexp : ∀ g : L' ≃ₐ[E] L', g ^ n' = 1) (hn : Module.finrank E F ∣ n')
    (u : (AdeleRing (𝓞 E) E)ˣ) :
    (Units.map (genuineBaseChange E F).β.toMonoidHom u) ^ (n' / Module.finrank E F) ∈
      principalIdeles (𝓞 F) F ⊔ (genuineBaseChange F N).idelicNorm.range := by sorry
