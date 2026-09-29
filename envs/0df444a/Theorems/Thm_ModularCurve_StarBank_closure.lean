-- Prove2me | Theorems.Thm_ModularCurve_StarBank_closure
-- name    : ModularCurve.StarBank.closure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/506259df-1746-5601-8078-8d4459e1363c
-- title:
--   Divisibility G∘ R ∣ c Gᵖ⁺¹ from q-expansion identities
-- statement:
--   Let $K$ be an algebraically closed field, $p$ a prime, $\zeta$ a unit of $K$, $M$ a natural number and $G, R \in K[X]$. Write $j = q^{-1}\cdot\mathrm{jNum}$ for the Laurent series `jqModC K`, the image in $K((q))$ of the integral power series $E_4^3\cdot\mathrm{dedekindEtaUnitInv}$ shifted by $q^{-1}$, and $\Delta = q\prod_{n\ge 1}(1-q^n)^{24}$ for the Laurent series `HahnSeries.single 1 1 * ofPowerSeries (etaProd)^24` over $K$; for a unit $u$ let $f(uq)$ denote `qTwist u f`, the ring endomorphism multiplying the coefficient of $q^k$ by $u^k$, and let $f(q^N)$ denote `qExpand K N f`, the ring endomorphism multiplying all exponents by $N$ (so $j(q^p)$ is `jqNModC K p`). Four identities in $K((q))$, respectively in $K((q))[X]$, are assumed: $G(j)\,\Delta^M = 1$; $R(j) = j(q^p)$; the coefficientwise image of $R$ in $K((q))[X]$ minus the constant $j(q^p)$ equals $\prod_{b=0}^{p-1}\bigl(X - j(\zeta^b q)\bigr)$; and the norm identity $\bigl(\prod_{b=0}^{p-1}\Delta(\zeta^b q)\bigr)\cdot\Delta(q^{p^2}) = \bigl(\prod_{b=0}^{p-1}\zeta^b\bigr)\cdot\Delta(q^p)^{p+1}$. The conclusion is that there exists $c \in K$, $c \neq 0$, such that $G(R(X))$ divides $c\,G(X)^{p+1}$ in $K[X]$.
--
--   The third hypothesis exhibits $R$ as the monic degree-$p$ polynomial whose roots are the $q$-twisted expansions $j(\zeta^b q)$, and the fourth is the norm identity for the discriminant function along the same twists; the conclusion expresses that the root set of $G$ is stable under passing from $\beta$ to the roots of $R(X) - R(\beta)$, in the strong form of a divisibility in $K[X]$. It is the closure step used by [`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank) in the formal $q$-expansion treatment of the modular equation relating $j(q)$ and $j(q^p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_closure.lean

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.StarBank.closure {K : Type*} [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) {M : ℕ} {G R : Polynomial K}
    (hstar : Polynomial.aeval (jqModC K) G *
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1)
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p)
    (hpress : R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))))
    (hnorm : (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1)) :
    ∃ c : K, c ≠ 0 ∧ G.comp R ∣ Polynomial.C c * G ^ (p + 1) := by sorry
