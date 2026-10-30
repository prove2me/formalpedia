-- Prove2me | Theorems.Thm_JuschenkoMonod_exists_orbitIndexing_and_injective_and_hasUbiquitousPatternProperty_range_of_isMinimal
-- name    : JuschenkoMonod.exists_orbitIndexing_and_injective_and_hasUbiquitousPatternProperty_range_of_isMinimal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:29:09.558194+00:00
-- url     : https://prove2.me/theorems/6ac50338-9ef7-402e-93bc-6c2398cd90be
-- title:
--   Lemma 4.2 — for minimal T, π_p is an injective homomorphism and its image has the ubiquitous pattern property
-- statement:
--   Let $T$ be a minimal homeomorphism of a Cantor space $C$, and let $p \in C$. Then:
--   - there is a group homomorphism $\pi_p\colon [[T]] \to W(\mathbf Z)$ with $g(T^jp) = T^{\pi_p(g)(j)}p$ for every $g \in [[T]]$ and $j \in \mathbf Z$;
--   - every group homomorphism $\varphi\colon [[T]] \to W(\mathbf Z)$ with $g(T^jp) = T^{\varphi(g)(j)}p$ for all $g$ and $j$ is injective, and its image $\varphi([[T]])$, a subgroup of $W(\mathbf Z)$, has the ubiquitous pattern property.
--
--   *Formalization note.* The lemma names "the injective homomorphism $\pi_p$". The statement asserts that a homomorphism satisfying the defining requirement of $\pi_p$ exists, and that every such homomorphism is injective with an image having the ubiquitous pattern property. That the requirement determines $\pi_p$ is the p. 786 milestone on $\pi_p$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 786, Lemma 4.2

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_CantorSystems
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem exists_orbitIndexing_and_injective_and_hasUbiquitousPatternProperty_range_of_isMinimal
    (C : Type*) [TopologicalSpace C] (hC : CantorSystems.IsCantorSpace C) (T : C ≃ₜ C)
    (hT : IsMinimal T) (p : C) :
    (∃ φ : fullGroup T →* IntervalExchange.wobbling ℤ,
        IsOrbitIndexing T p fun g => (φ g : Equiv.Perm ℤ)) ∧
      ∀ φ : fullGroup T →* IntervalExchange.wobbling ℤ,
        (IsOrbitIndexing T p fun g => (φ g : Equiv.Perm ℤ)) →
          Function.Injective φ ∧
            HasUbiquitousPatternProperty (φ.range.map (IntervalExchange.wobbling ℤ).subtype) := by
  sorry

end JuschenkoMonod
