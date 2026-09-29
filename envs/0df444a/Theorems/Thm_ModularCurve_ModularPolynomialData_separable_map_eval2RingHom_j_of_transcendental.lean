-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_eval2RingHom_j_of_transcendental
-- name    : ModularCurve.ModularPolynomialData.separable_map_eval2RingHom_j_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/84a4b29f-57a3-5708-a6f1-1e655651fe33
-- title:
--   Separability of Φ_N(j(E),Y) for transcendental j(E)
-- statement:
--   Let $K$ be a field, let $N$ be a nonzero natural number, and let `data` be a modular polynomial datum of level $N$: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ (i.e. `data.Φ : Polynomial (Polynomial ℤ)`) that is monic in $Y$, of degree in $Y$ equal to $\sum_{d \mid N,\ d \text{ squarefree}} N/d$, and such that substituting the Laurent-series $q$-expansion of $j$ for $X$ and the series $j(q^N)$ for $Y$ (the ring homomorphism `evalAtJ`, induced by $X \mapsto$ `jq`, applied to `jqN N`) gives $0$. Let $L$ be an algebraically closed field equipped with a $K$-algebra structure, assume $N \neq 0$ in $L$, and let $E$ be a Weierstrass curve over $L$ that is elliptic, whose $j$-invariant $j(E) \in L$ is transcendental over $K$. The conclusion is that the polynomial in $L[Y]$ obtained from $\Phi$ by applying coefficientwise the ring homomorphism $\mathbb{Z}[X] \to L$ sending $X \mapsto j(E)$ — that is, $\Phi(j(E), Y)$ — is separable, i.e. coprime to its derivative.
--
--   This is the classical statement that the modular polynomial $\Phi_N(X,Y)$, specialised at a generic (here: transcendental over the base field $K$) $j$-invariant, has $\psi(N)$ distinct roots, one for each cyclic subgroup of order $N$ of $E$. It supplies the separability input for the Galois-descent step identifying the $j$-invariants of $N$-isogenous quotients defined over subfields, used in [`WeierstrassCurve.DrinfeldGlobal.exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_separable_map_eval2RingHom_j_of_transcendental.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem ModularCurve.ModularPolynomialData.separable_map_eval2RingHom_j_of_transcendental
    (K : Type u) [Field K] (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (L : Type v) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra K L]
    (hN : (N : L) ≠ 0) (E : WeierstrassCurve L) [E.IsElliptic] (hE : Transcendental K E.j) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) E.j)).Separable := by sorry
