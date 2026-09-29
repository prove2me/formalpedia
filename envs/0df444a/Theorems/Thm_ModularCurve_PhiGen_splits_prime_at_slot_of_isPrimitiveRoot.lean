-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot
-- name    : ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/d9095e24-91b1-5043-93c5-196e9d87e5b0
-- title:
--   Prime-level splitting of Φₚ at the slot uq^e
-- statement:
--   Let $K$ be a field, $p$ a prime, and $\zeta \in K^\times$ a unit whose image in $K$ is a primitive $p$-th root of unity (so $K$ has characteristic $\neq p$). Let `data` be a level-$p$ modular polynomial datum: a polynomial $\Phi \in \mathbb{Z}[X][Y]$, monic, of degree $\sum_{d \mid p,\ d \text{ squarefree}} p/d = p+1$ in $Y$, satisfying $\Phi(j(q), j(q^p)) = 0$ in $\mathbb{Q}((q))$, where $j$ denotes the formal $q$-expansion `jq` and the inner variable is evaluated at $j(q)$. Let $e$ be a nonzero natural number and $u \in K^\times$. Write $j_K = q^{-1}\cdot(\text{image of } E_4^3/\text{(eta factor)})$ for the $j$-expansion `jqModC K` over $K$, and for a unit $v$ and nonzero $N$ let $v, N$ act on $K((q))$ by the ring homomorphisms `qTwist` ($q \mapsto vq$, i.e. the $k$-th coefficient is multiplied by $v^k$) and `qExpand` ($q \mapsto q^N$). Then, in $K((q))[Y]$, specialising the integer coefficients of $\Phi$ into $K((q))$ and its inner variable at $j_K(u^p q^{pe})$ yields $$\Phi\bigl(j_K(u^pq^{pe}), Y\bigr) = \bigl(Y - j_K(u^{p^2}q^{p^2e})\bigr)\prod_{b=0}^{p-1}\bigl(Y - j_K(u\zeta^b q^{e})\bigr).$$
--
--   This is the classical factorisation of the level-$p$ modular polynomial, $\Phi_p(j(p\tau), Y) = (Y - j(p^2\tau))\prod_{b<p}(Y - j((\tau+b)/p))$, in the formal $q$-expansion model over an arbitrary field containing a primitive $p$-th root of unity, and stated at an arbitrary slot $s = uq^e$ rather than only at $s = q$. It supplies the list of the $p+1$ expansions lying above a given conjugate one step up a tower of $q$-expansion fields, and is used in the construction of monic factorisations of $\Phi$ over such fields, in the proof that $j(q^{dp})$ lies in the relevant modular function field, and in the chart computations on $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K (p * e) (qTwist (u ^ p) (jqModC K)))) = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)))) * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) := by sorry
