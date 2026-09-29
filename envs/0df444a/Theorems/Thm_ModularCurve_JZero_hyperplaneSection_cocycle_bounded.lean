-- Prove2me | Theorems.Thm_ModularCurve_JZero_hyperplaneSection_cocycle_bounded
-- name    : ModularCurve.JZero.hyperplaneSection_cocycle_bounded
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/2048de6d-3258-5180-b4be-9c84b43d8f16
-- title:
--   Boundedness of the hyperplane-section Chow cocycle
-- statement:
--   Fix $N \ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series. Let $s : \mathrm{Fin}\,r \to \bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space $L(E)$, where $E =$ `embDivisor N` is $(2g+1)$ times the divisor of the cusp at infinity and $2g+1 =$ `embDegree N` with $g$ the genus of $\bar F_N$. The assertion is the existence of a single real constant $C$ (depending only on $N$ and $s$) such that for every ring homomorphism $\sigma : \overline{\mathbb Q} \to \mathbb C$ the following holds, under the hypothesis that the Chow reciprocity identity `ChowReciprocity s (embDivisor N) k' u' B'` holds for every $k' \in \mathbb N$, every nonzero $u' \in L(k'E)$ and every divisor $B'$ with $B'(w) = \mathrm{ord}_w(u') + k'E(w)$ for all places $w$: for all covectors $a, a', c : \mathrm{Fin}\,r \to \overline{\mathbb Q}$ with the linear sections $\sum_i a_i s_i$, $\sum_i a'_i s_i$, $\sum_i c_i s_i$ nonzero, and all divisors $Z_a, Z_{a'}, Z_c$ given pointwise by $Z_a(w) = \mathrm{ord}_w(\sum_i a_i s_i) + E(w)$ and likewise for $a'$ and $c$, such that $Z_a$ and $Z_c$ have disjoint supports ($Z_a(w) = 0$ or $Z_c(w) = 0$ at every place $w$) and $Z_{a'}$ and $Z_c$ likewise, one has $|G_\sigma(a,c) - G_\sigma(a',c)| \le C$, where $G_\sigma(a,c)$ is the difference of the two brackets $\log\|\sigma(F_{Z_c}(a))\| - \sum_z Z_c(z)\log \sup_i\|\sigma(x_z)_i\| - (2g+1)\log\sup_i\|\sigma(a_i)\|$ and $\log\|\sigma(F_{Z_a}(c))\| - \sum_y Z_a(y)\log\sup_i\|\sigma(x_y)_i\| - (2g+1)\log\sup_i\|\sigma(c_i)\|$; here $F_Z =$ `chowForm s Z` is the product over places $w$ of $(\sum_i \mathrm{ev}_w(s_i/s_{\mathrm{pivot}})\,X_i)^{Z(w)^+}$ and $x_w =$ `evalVec s w` is the pivot-normalised coordinate vector of $w$.
--
--   This is the boundedness (cocycle) estimate for the local height defect of hyperplane sections in the embedding of the modular curve of level $N$ by the complete linear system $L((2g+1)\infty)$: the quantity $G_\sigma(a,c)$, antisymmetric up to sign in $a$ and $c$, measures how closely the hyperplane $a$ approaches the points of $Z_c$ against how closely $c$ approaches those of $Z_a$, and the theorem says its dependence on $a$ is bounded independently of $\sigma$ and of the data. It feeds into [`ModularCurve.JZero.pencil_secProd_chowForm_two_sided`](thm.html#ModularCurve.JZero.pencil_secProd_chowForm_two_sided) in the construction of the height form on the degree-zero divisor class group of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_hyperplaneSection_cocycle_bounded.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.hyperplaneSection_cocycle_bounded (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ C : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ),
      (∀ (k' : ℕ) (u' : modularFunctionFieldBar N)
          (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
          u' ≠ 0 → u' ∈ riemannRochSpace ((k' : ℤ) • embDivisor N) →
          (∀ w, B' w = w.ord u' + ((k' : ℤ) • embDivisor N) w) →
          ChowReciprocity s (embDivisor N) k' u' B') →
      ∀ (a a' c : Fin r → AlgebraicClosure ℚ)
        (Za Za' Zc : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        linSec s a ≠ 0 → linSec s a' ≠ 0 → linSec s c ≠ 0 →
        (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) →
        (∀ w, Za' w = w.ord (linSec s a') + embDivisor N w) →
        (∀ w, Zc w = w.ord (linSec s c) + embDivisor N w) →
        (∀ w, Za w = 0 ∨ Zc w = 0) → (∀ w, Za' w = 0 ∨ Zc w = 0) →
        |((Real.log ‖σ (MvPolynomial.eval a (chowForm s Zc))‖
              - (Zc.sum fun z n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s z i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (a i)‖))
            - (Real.log ‖σ (MvPolynomial.eval c (chowForm s Za))‖
              - (Za.sum fun y n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (c i)‖)))
          - ((Real.log ‖σ (MvPolynomial.eval a' (chowForm s Zc))‖
              - (Zc.sum fun z n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s z i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (a' i)‖))
            - (Real.log ‖σ (MvPolynomial.eval c (chowForm s Za'))‖
              - (Za'.sum fun y n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (c i)‖)))| ≤ C := by sorry
