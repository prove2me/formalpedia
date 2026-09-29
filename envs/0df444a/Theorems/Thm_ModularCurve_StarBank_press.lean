-- Prove2me | Theorems.Thm_ModularCurve_StarBank_press
-- name    : ModularCurve.StarBank.press
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/f155204d-9081-5d43-beed-383c2e0ac1f8
-- title:
--   Monicity and splitting of a polynomial relation R(j(q))=j(qᵖ)
-- statement:
--   Let $K$ be a field, $p$ a prime, and $\zeta$ a unit of $K$ whose image in $K$ is a primitive $p$-th root of unity. Write $j(q) :=$ `jqModC K` for the Laurent series $q^{-1}\cdot\iota(E_4^3\,\eta^{-1}\text{-unit})$ over $K$, i.e. the formal power series `jNum` $=$ `eisenstein4`$^3\cdot$`dedekindEtaUnitInv` with its integer coefficients pushed into $K$, shifted by the monomial $q^{-1}$; and write $j(q^p) :=$ `jqNModC K p` for its image under `qExpand K p`, the ring endomorphism of $K((q))$ that multiplies all exponents by $p$ (substitution $q \mapsto q^p$). Let $R \in K[X]$ be a polynomial with $R(j(q)) = j(q^p)$ in $K((q))$. Then $R$ is monic, its natural degree is exactly $p$, and in $K((q))[X]$ one has the identity
--   $$R^{K((q))}(X) - j(q^p) \;=\; \prod_{b=0}^{p-1}\bigl(X - \mathrm{qTwist}(\zeta^b)\,j(q)\bigr),$$
--   where $R^{K((q))}$ is $R$ with coefficients mapped along $K \to K((q))$, the subtracted term is the constant polynomial with value $j(q^p)$, and `qTwist` $(\zeta^b)$ is the ring endomorphism of $K((q))$ multiplying the coefficient of $q^k$ by $\zeta^{bk}$, i.e. the substitution $q \mapsto \zeta^b q$ applied to $j(q)$.
--
--   This is the formal $q$-expansion form of the classical observation that a hypothetical polynomial relation $j(q^p) = R(j(q))$ forces $R$ to be monic of degree $p$ with $R(X) - j(q^p)$ split by the $p$ twists $j(\zeta^b q)$, the twists fixing $j(q^p)$ and being pairwise distinct precisely because $\zeta$ has exact order $p$. It is used by [`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank), in the course of ruling out such a relation and hence establishing the relevant non-integrality/degree statement for the modular correspondence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_press.lean

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.StarBank.press {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) {R : Polynomial K}
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p) :
    R.Monic ∧ R.natDegree = p ∧
      R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by sorry
