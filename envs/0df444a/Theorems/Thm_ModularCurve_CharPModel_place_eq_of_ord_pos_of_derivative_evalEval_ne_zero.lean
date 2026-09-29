-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_place_eq_of_ord_pos_of_derivative_evalEval_ne_zero
-- name    : ModularCurve.CharPModel.place_eq_of_ord_pos_of_derivative_evalEval_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/a817a0e7-09f7-5fe5-8045-0892eb552130
-- title:
--   Places of the modular function field determined by smooth coordinates
-- statement:
--   Let $k$ be a field and $N$ a positive integer, and let `data` be a `ModularPolynomialData N`, that is, a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic in $Y$, of degree $\psi(N)=\sum_{d \mid N,\ d \text{ squarefree}} N/d$ in $Y$, and which annihilates the pair of $q$-expansions $(j, j_N)$. Write $\bar\Phi$ for the image of $\Phi$ under coefficientwise reduction along $\mathbb{Z} \to k$. Let $s, t \in k$ satisfy $\bar\Phi(s,t) = 0$ (substituting $X \mapsto s$, $Y \mapsto t$) and $(\partial \bar\Phi/\partial Y)(s,t) \neq 0$. Let $F =$ `modularFunctionFieldC k N` be the subfield of the field of Laurent series over $k$ generated over $k$ by the two series $\tilde j =$ `jqModC k` $= q^{-1}\cdot\overline{\mathrm{jNum}}$ and $\tilde j_N =$ `jqNModC k N`, the image of $\tilde j$ under $q \mapsto q^N$. Let $P$ and $Q$ be places of $F$ over $k$, i.e. proper valuation subrings of $F$ containing $k$ and which are principal ideal rings, and suppose that for each of $P$ and $Q$ the associated order function (the negative logarithm of the adic valuation of the corresponding height-one prime) is strictly positive on both $\tilde j - s$ and $\tilde j_N - t$. Then $P = Q$.
--
--   This is the uniqueness half of the correspondence between places of the modular function field in characteristic $p$ (or over any field $k$) and points of the reduced plane model $\bar\Phi_N(X,Y)=0$: at a point where the $Y$-derivative does not vanish the local ring is a discrete valuation ring, and a valuation ring dominating it must coincide with it, so the coordinates $(s,t)$ pin down at most one place. It relies on the discreteness statement [`ModularCurve.CharPModel.isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero`](thm.html#ModularCurve.CharPModel.isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero), and is used in the analysis of fibres and of specialisation of places on the modular curve, in particular for the existence of places with prescribed order and inertia behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_place_eq_of_ord_pos_of_derivative_evalEval_ne_zero.lean

import Mathlib.Algebra.Polynomial.Bivariate
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve Polynomial

theorem ModularCurve.CharPModel.place_eq_of_ord_pos_of_derivative_evalEval_ne_zero
    {k : Type*} [Field k] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (s t : k)
    (hroot : (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).evalEval s t = 0)
    (hder : (Polynomial.derivative
        (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval s t ≠ 0)
    (P Q : Place k (modularFunctionFieldC k N))
    (hPj : 0 < P.ord (⟨jqModC k, jqModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) s))
    (hPjN : 0 < P.ord (⟨jqNModC k N, jqNModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) t))
    (hQj : 0 < Q.ord (⟨jqModC k, jqModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) s))
    (hQjN : 0 < Q.ord (⟨jqNModC k N, jqNModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) t)) :
    P = Q := by sorry
