-- Prove2me | Theorems.Thm_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg
-- name    : MonoidAlgebra.mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/6de0abc5-9ad6-5f64-b841-4744655dedb9
-- title:
--   Non-finite Adams-stable orders in ℚ[ℤ/q] are the augmentation order
-- statement:
--   Let $p$ be a prime and let $q$ be a prime, and write $R = \mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator (in lowest terms) is coprime to $p$. Let $B$ be an $R$-subalgebra of the group algebra $V = \mathbb{Q}[\mathbb{Z}/q]$, realised as `MonoidAlgebra ℚ (Multiplicative (ZMod q))`, subject to four hypotheses: $B$ is finitely generated as an $R$-algebra; the augmentation (the coalgebra counit $\varepsilon \colon V \to \mathbb{Q}$, summing coefficients) maps $B$ into $R$; for every $v \in V$ there is an integer $n > 0$ with $n v \in B$, so $\mathbb{Q} \cdot B = V$; and $B$ is stable under the Adams operation $u \mapsto u^{a}$ on group-like elements, i.e. under the algebra map induced by the $a$-th power map on $\mathbb{Z}/q$, for every $a$ coprime to $q$. Assume further that $B$ is *not* finitely generated as an $R$-module. Then for every $v \in V$ one has $v \in B$ if and only if $\varepsilon(v) \in R$; equivalently $B = R \cdot 1 \oplus \ker \varepsilon$.
--
--   This is the classification, at the level of the localisation $\mathbb{Z}_{(p)} \subset \mathbb{Q}$, of Adams-stable orders of finite type in the group algebra of $\mathbb{Z}/q$ with integral augmentation: such an order is either finite over $\mathbb{Z}_{(p)}$ or else is the full "punctured" order $\{v : \varepsilon(v) \in \mathbb{Z}_{(p)}\}$, which under $\mathbb{Q}[\mathbb{Z}/q] \cong \mathbb{Q} \times \mathbb{Q}(\zeta_q)$ is $\mathbb{Z}_{(p)} \times \mathbb{Q}(\zeta_q)$. It is used in the rigidity analysis of Hopf algebras of prime rank, namely by [`HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two`](thm.html#HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two), to exclude non-finite candidates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MonoidAlgebra.mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg
    (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
    (B : Subalgebra (GaloisRep.ratLocalizedAt p) (MonoidAlgebra ℚ (Multiplicative (ZMod q))))
    (hfg : B.FG)
    (haug : ∀ b ∈ B, Coalgebra.counit (R := ℚ) b ∈ GaloisRep.ratLocalizedAt p)
    (hsat : ∀ v : MonoidAlgebra ℚ (Multiplicative (ZMod q)), ∃ n : ℕ, 0 < n ∧ (n : ℚ) • v ∈ B)
    (hadams : ∀ a : ℕ, a.Coprime q → ∀ b ∈ B,
      MonoidAlgebra.mapDomainAlgHom ℚ ℚ (powMonoidHom a) b ∈ B)
    (hinf : ¬ (Subalgebra.toSubmodule B).FG) :
    ∀ v : MonoidAlgebra ℚ (Multiplicative (ZMod q)),
      v ∈ B ↔ Coalgebra.counit (R := ℚ) v ∈ GaloisRep.ratLocalizedAt p := by sorry
