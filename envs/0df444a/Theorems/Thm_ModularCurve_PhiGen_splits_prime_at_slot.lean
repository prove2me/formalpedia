-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot
-- name    : ModularCurve.PhiGen.splits_prime_at_slot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/6645bdfa-6ae3-5bd7-ad42-8762b3625fa3
-- title:
--   Twisted prime-level splitting of the modular polynomial Φₚ
-- statement:
--   Let $K$ be a field of characteristic zero (a $\mathbb{Q}$-algebra), let $N$ be a nonzero natural number, and let $\zeta \in K^{\times}$ be a unit whose underlying element is a primitive $N$-th root of unity. Let $p$ be a prime dividing $N$, and let `data` provide a level-$p$ modular polynomial, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(p) = \sum_{d \mid p,\ d \text{ squarefree}} p/d = p+1$ in $Y$ satisfying $\Phi(j(q), j(q^{p})) = 0$ for the Laurent-series $j$-expansion $j_q = q^{-1}\cdot(\text{power series } j_{\mathrm{Num}})$ over $\mathbb{Q}$. Let $e$ be a nonzero natural number and $u \in K^{\times}$. Write $\hat{\jmath}_{w}(t^{m})$ for the Laurent series over $K$ obtained from the image of $j_q$ in $K((t))$ by the twist multiplying the coefficient in degree $k$ by $w^{k}$ and then by the exponent dilation $t \mapsto t^{m}$. The conclusion is an identity in $K((t))[Y]$: substituting $\hat{\jmath}_{u^{p}}(t^{pe})$ for the inner variable of $\Phi$ (coefficients mapped through $\mathbb{Z} \to K((t))$) gives $$\Bigl(Y - \hat{\jmath}_{u^{p^{2}}}(t^{p\cdot pe})\Bigr)\prod_{b=0}^{p-1}\Bigl(Y - \hat{\jmath}_{u\zeta^{b(N/p)}}(t^{e})\Bigr),$$ a product of $p+1$ monic linear factors.
--
--   This is the classical splitting of the level-$p$ modular equation, $\Phi_p(j(q^{p}), Y) = (Y - j(q^{p^{2}}))\prod_{b<p}(Y - j(\zeta_p^{b} q))$, transported to an arbitrary twisted and dilated $q$-parameter $u t^{e}$, with $\zeta^{N/p}$ serving as the primitive $p$-th root of unity. It is the basic local step in the purely algebraic determination of $[\mathbb{Q}(j,j_N):\mathbb{Q}(j)] = \psi(N)$, i.e. of the irreducibility of the modular polynomial $\Phi_N$ over $\mathbb{Q}(j)$, and is invoked throughout that development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.splits_prime_at_slot {K : Type*} [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N) (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq)))) = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq)))) * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))) := by sorry
