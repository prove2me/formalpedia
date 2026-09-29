-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_splits_of_prime
-- name    : ModularCurve.PhiGen.splits_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/d0261f5d-094d-5699-ac34-71cdc26fe4ff
-- title:
--   Prime-level modular polynomial splits over any field with ζₚ
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $p$ be a prime, let $\zeta$ be a unit of $K$ whose underlying element is a primitive $p$-th root of unity, and let `data` be any modular polynomial datum of level $p$, that is, a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ that is monic in $Y$, has $Y$-degree $\psi(p)=\sum_{d \mid p,\ d \text{ squarefree}} p/d$, and satisfies $\Phi(j(q), j(q^p)) = 0$ in the Laurent series field over $\mathbb{Q}$, where coefficients in $\mathbb{Z}[X]$ are evaluated at the $q$-expansion `jq` of $j$ by `evalAtJ`. The conclusion is an identity of polynomials over `LaurentSeries K`: applying to each coefficient of $\Phi$ the ring homomorphism "evaluate at `jq`, then substitute $t \mapsto t^{p}$ (multiply all exponents by $p$), then embed the coefficients into $K$" yields $\prod_{i \in \mathrm{Fin}(p+1)} \bigl(Y - \mathrm{conj}\,p\,\zeta\,i\bigr)$. Here the $i$-th factor's root is obtained from the image of `jq` in `LaurentSeries K` by twisting the variable by $\zeta^{ab}$ and then multiplying exponents by $a^{2}$, with $(a,b) = (p,0)$ for $i = 0$ and $(a,b) = (1, i-1)$ otherwise.
--
--   This is the classical factorisation of the modular equation of prime level, $\Phi_p(j(q),Y) = (Y - j(q^{p}))\prod_{b=0}^{p-1}(Y - j(\zeta^{b} q^{1/p}))$, indexed by the $p+1$ cosets of $\Gamma_0(p)$ in $\mathrm{SL}_2(\mathbb{Z})$, here in the form of an identity of polynomials over a Laurent series field. Compared with [`ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq`](thm.html#ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq) it carries no descent hypothesis on the coefficients of the datum, being stated for every level-$p$ datum and every field with a primitive $p$-th root of unity; it feeds the splitting statements [`ModularCurve.PhiGen.splits_prime_at_slot`](thm.html#ModularCurve.PhiGen.splits_prime_at_slot) and its variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_splits_of_prime.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.splits_of_prime {K : Type*} [Field K] [Algebra ℚ K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) : data.Φ.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) = phiProd p (conj p ζ) := by sorry
