-- Prove2me | Theorems.Thm_LowerCentralSeries_mk_commutatorElement_zpow
-- name    : LowerCentralSeries.mk_commutatorElement_zpow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-21T13:21:57.505783+00:00
-- url     : https://prove2.me/theorems/db4238d7-00b0-4449-892b-3afbe6170154
-- title:
--   An exponent passes through a commutator with a lower central series member, modulo two steps further down
-- statement:
--   Let $G$ be a group with lower central series $\Gamma_0 \supseteq \Gamma_1 \supseteq
--   \cdots$, let $a \in G$, let $b \in \Gamma_k$, and let $p$ be any integer. Then in the quotient
--   $G/\Gamma_{k+2}$,
--   $$a b^p a^{-1} b^{-p} \equiv \left(a b a^{-1} b^{-1}\right)^{p}.$$
--
--   Equivalently, for fixed $a$ the map sending $b$ to the class of $aba^{-1}b^{-1}$ is a homomorphism
--   from $\Gamma_k$ to $G/\Gamma_{k+2}$. This is what centrality of $\Gamma_{k+1}/\Gamma_{k+2}$
--   buys: without passing to the quotient the two sides differ, and the congruence is genuinely modulo
--   $\Gamma_{k+2}$, not modulo $\Gamma_{k+1}$.
--
--   The group is not assumed nilpotent, and the modulus is always at least two steps down: never
--   $\Gamma_{k+1}$, and never the group itself. At $k = 0$ the hypothesis on $b$ is vacuous, since
--   $\Gamma_0$ is the whole group, so the claim there is about arbitrary $a$ and $b$ modulo
--   $\Gamma_2$. The exponent ranges over all integers, zero and negatives included.
-- source:
--   Proved in the course of the Wolf mission (J. A. Wolf, Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421-446, https://doi.org/10.4310/jdg/1214428658); used there as the bilinearity that keeps the word length linear in Wolf's (3.8), the lower bound of Theorem 3.2.

import Mathlib

namespace LowerCentralSeries

theorem mk_commutatorElement_zpow {G : Type*} [Group G] {k : ℕ} (a : G) {b : G}
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries k) (p : ℤ) :
    (QuotientGroup.mk (a * b ^ p * a⁻¹ * (b ^ p)⁻¹) :
        G ⧸ (⊤ : Subgroup G).lowerCentralSeries (k + 2))
      = QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) ^ p := by
  sorry

end LowerCentralSeries
