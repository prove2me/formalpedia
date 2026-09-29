-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot
-- name    : ModularCurve.PhiGen.splits_prime_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/c5ce1ac5-ca3f-50c6-9b8b-d8bd50e546b9
-- title:
--   Splitting of Φₚ(j(qᵖ),Y) over K((q))
-- statement:
--   Let $K$ be a field, $p$ a prime, and $\zeta \in K^\times$ a unit whose underlying element is a primitive $p$-th root of unity in $K$. Let `data` be a level-$p$ modular polynomial datum: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic in $Y$, of degree $\psi(p) = \sum_{d \mid p,\ d \text{ squarefree}} p/d = p+1$, and which satisfies $\Phi(j(q), j(q^p)) = 0$ in $\mathbb{Q}((q))$, where $j(q)$ is the $q$-expansion `jq` and $j(q^p)$ its substitution $q \mapsto q^p$. Write $j(q) \in K((q))$ for `jqModC K`, namely $q^{-1}$ times the power series $E_4^3 \cdot \eta^{-24}$ with its integer coefficients read in $K$; write $j(q^N)$ for the image of $j(q)$ under the ring endomorphism of $K((q))$ multiplying all exponents by $N$, and $j(\zeta^b q)$ for the twist multiplying the coefficient of $q^k$ by $\zeta^{bk}$. The assertion is that, after substituting $X \mapsto j(q^p)$ in the coefficients of $\Phi$ (integers mapped into $K((q))$), one has in $K((q))[Y]$
--   $$\Phi\bigl(j(q^p), Y\bigr) = \bigl(Y - j(q^{p^2})\bigr) \prod_{b=0}^{p-1} \bigl(Y - j(\zeta^b q)\bigr).$$
--
--   This is the classical factorisation of the level-$p$ modular polynomial specialised at the seed $j(q^p)$, whose roots are the $j$-invariants of the $p+1$ cyclic $p$-isogenous curves; the only hypothesis on the coefficient field is the presence of a primitive $p$-th root of unity, which in particular excludes characteristic $p$. Unlike the companion statement [`ModularCurve.PhiGen.splits_of_prime`](thm.html#ModularCurve.PhiGen.splits_of_prime), no $\mathbb{Q}$-algebra structure on $K$ is assumed, and the factorisation is used to identify the modular polynomials at levels $2$ and $3$ in [`ModularCurve.ModularPolynomialData.phi_eq_phiTwo`](thm.html#ModularCurve.ModularPolynomialData.phi_eq_phiTwo) and [`ModularCurve.ModularPolynomialData.phi_eq_phiThree`](thm.html#ModularCurve.ModularPolynomialData.phi_eq_phiThree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.splits_prime_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K p (jqModC K))) = (Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K))) * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by sorry
