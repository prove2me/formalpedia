-- Prove2me | Theorems.Thm_ModularCurve_StarBank_delta_pow_ne
-- name    : ModularCurve.StarBank.delta_pow_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/41f7025d-90bb-59c1-8f6a-62a27ddf93ef
-- title:
--   In characteristic ℓ, Δᵖ is never γ Δ(qᵖ)
-- statement:
--   Let $K$ be a commutative ring, $\ell$ a prime, and suppose $K$ has characteristic $\ell$; let $p$ be a prime with $p \neq \ell$, and let $\gamma \in K$. Work in the Laurent series ring $K(\!(q)\!)$, realised as Hahn series over $\mathbb{Z}$, and set $\Delta$ to be the product of the monomial $q$ (the Hahn series `HahnSeries.single (1 : ℤ) (1 : K)`) with the twenty-fourth power of the image in $K(\!(q)\!)$ of the power series $\prod_{n \ge 1}(1 - X^{n})$ over $\mathbb{Z}$ (the project's `etaProd`), its coefficients pushed into $K$ along $\mathbb{Z} \to K$; thus $\Delta = q\prod_{n\ge 1}(1-q^{n})^{24}$. Let $\mathrm{qExpand}\,K\,p$ be the ring endomorphism of $K(\!(q)\!)$ obtained by re-indexing exponents along multiplication by $p$ on $\mathbb{Z}$, that is, the substitution $q \mapsto q^{p}$. The assertion is that $\Delta^{p} \neq \gamma \cdot \mathrm{qExpand}\,K\,p\,(\Delta)$, i.e. $\Delta(q)^{p}$ is not the constant $\gamma$ times $\Delta(q^{p})$, for any such $\gamma$.
--
--   The statement rules out the one relation that would be compatible with all the congruence constraints in the characteristic-$\ell$ study of the $q$-expansions attached to $X_0(N)$, the hypothesis $p \neq \ell$ being essential since for $p = \ell$ the identity holds with $\gamma = 1$ (raising a series with coefficients from the prime field to the $\ell$-th power substitutes $q \mapsto q^{\ell}$, as recorded in [`ModularCurve.map_intCast_pow_char_eq_qExpand`](thm.html#ModularCurve.map_intCast_pow_char_eq_qExpand)). It is used by [`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_delta_pow_ne.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.StarBank.delta_pow_ne (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) (γ : K) :
    (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p ≠
      HahnSeries.C γ * qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by sorry
