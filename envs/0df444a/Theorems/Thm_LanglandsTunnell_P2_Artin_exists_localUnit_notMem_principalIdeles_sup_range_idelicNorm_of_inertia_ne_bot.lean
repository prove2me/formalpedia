-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
-- name    : LanglandsTunnell.P2.Artin.exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/5b00915a-5b02-5542-aa60-07ba0b533fe0
-- title:
--   Ramified place yields local unit outside the reciprocity kernel
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an $E$-algebra such that $F/E$ is Galois, and assume the degree $[F:E] = \mathrm{finrank}_E F$ is a prime number. Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_E$, and let $\mathrm{primeAbove}\,E\,F\,v$ be the chosen prime ideal of $\mathcal{O}_F$ lying over $v$ (the one extracted from the existence statement `exists_prime_over`); assume its inertia subgroup in $\mathrm{Gal}(F/E) = F \simeq_{\mathrm{alg}[E]} F$ is not the trivial subgroup. Then there is a unit $t$ of the completion $E_v$ such that both $t$ and $t^{-1}$ lie in the valuation ring $\mathcal{O}_{E_v}$ (`v.adicCompletionIntegers E`), and such that the following idèle of $E$ does not lie in the subgroup $\mathrm{principalIdeles}(\mathcal{O}_E, E) \sqcup \mathrm{range}((\mathrm{genuineBaseChange}\,E\,F).\mathrm{idelicNorm})$: the idèle obtained from the finite idèle whose component at $v$ is $t$ and whose components at all other finite places are $1$ (`localUnit`), transported into the full idèle group by the map $x \mapsto (1, x)$ (`finIncl`), so that it is also trivial at the infinite places. Here $\mathrm{principalIdeles}$ is the image of $E^\times$ under $E \to \mathbb{A}_E$, and $\mathrm{idelicNorm}$ is the map on unit groups induced by the algebra norm of $\mathbb{A}_F$ over $\mathbb{A}_E$ for the base change $\mathrm{genuineBaseChange}\,E\,F$; the join is taken in the lattice of subgroups of $(\mathbb{A}_E)^\times$.
--
--   The subgroup $\mathrm{principalIdeles} \sqcup \mathrm{range}(\mathrm{idelicNorm})$ is the kernel of the idelic Artin reciprocity map of the cyclic extension $F/E$, so the statement says that reciprocity is non-trivial on the local units at a place that ramifies in $F$ — the idelic form of the fact that ramified places divide the conductor. It is used in the construction of the finite-order Hecke characters and resolvent characters attached to a cubic resolvent field in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot.lean

import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LanglandsTunnell.P2.Artin.exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (hℓ : (Module.finrank E F).Prime) (v : HeightOneSpectrum (𝓞 E))
    (hv : (LanglandsTunnell.P2.Artin.primeAbove E F v).inertia (F ≃ₐ[E] F) ≠ ⊥) :
    ∃ t : (v.adicCompletion E)ˣ, (t : v.adicCompletion E) ∈ v.adicCompletionIntegers E ∧
      ((t⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ∈ v.adicCompletionIntegers E ∧
      Units.map (NumberField.AdelicLevel.finIncl (𝓞 E) E)
          (NumberField.AdelicLevel.localUnit (𝓞 E) E v t) ∉
        M4aHerbrand.principalIdeles (𝓞 E) E ⊔
          (M4aHerbrand.GenuineDescent.genuineBaseChange E F).idelicNorm.range := by sorry
