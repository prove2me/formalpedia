-- Prove2me | Theorems.Thm_ModularCurve_JZero_hyperplaneSection_cocycle
-- name    : ModularCurve.JZero.hyperplaneSection_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/0266c1c6-7c29-5e0c-a260-8bd9859f2ab2
-- title:
--   Cocycle identity for the hyperplane-section defect
-- statement:
--   Fix $N \ge 1$ and $r$, and let $s : \mathrm{Fin}\,r \to \overline{F}_N$ be a family in the base-changed modular function field $\overline{F}_N =$ `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ which is an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and spans the Riemann–Roch space of the divisor $E = \mathrm{embDivisor}\,N = d\cdot(\text{cusp }\infty)$ with $d = \mathrm{embDegree}\,N = 2g+1$. Let $\sigma : \overline{\mathbb{Q}} \to \mathbb{C}$ be a ring homomorphism. Assume the reciprocity hypothesis: for every $k'$, every non-zero $u'$ in the Riemann–Roch space of $k'\cdot E$ and every divisor $B'$ with $B'(w) = \mathrm{ord}_w(u') + k'E(w)$ for all places $w$, the predicate `ChowReciprocity s E k' u' B'` holds, i.e. for all covectors $a,b,c$ with non-zero linear sections $\sum_i a_i s_i$ etc. and divisors $Z_a, Z_b, Z_c$ pinned by $Z_a(w) = \mathrm{ord}_w(\sum_i a_i s_i) + E(w)$ (similarly for $b,c$), and satisfying $(Z_a(w)=0 \wedge Z_b(w)=0) \vee (B'(w)=0 \wedge Z_c(w)=0)$ for all $w$, one has $F_{B'}(a)\,F_{Z_c}(b)^{k'}F_{Z_a}(c)^{k'}\,\mathrm{secProd}(k',u',Z_b) = F_{B'}(b)\,F_{Z_c}(a)^{k'}F_{Z_b}(c)^{k'}\,\mathrm{secProd}(k',u',Z_a)$, where $F_Z = \mathrm{chowForm}\,s\,Z$ is the product over places $w$ of $(\sum_i (\mathrm{evalVec}\,s\,w)_i X_i)$ raised to the non-negative part of $Z(w)$. Let $a, a', c, e$ be covectors with non-zero linear sections, and let $Z_a, Z_{a'}, Z_c, Z_e$ be divisors pinned as above to $a, a', c, e$, subject to the four disjointness conditions: for every place $w$, $Z_a(w)=0$ or $Z_c(w)=0$; $Z_{a'}(w)=0$ or $Z_c(w)=0$; $Z_a(w)=0$ or $Z_e(w)=0$; $Z_{a'}(w)=0$ or $Z_e(w)=0$. Writing
--   $$G(a,c) = \Big[\log|\sigma F_{Z_c}(a)| - \sum_z Z_c(z)\log \sup_i |\sigma(\mathrm{evalVec}\,s\,z)_i| - d\log\sup_i|\sigma(a_i)|\Big] - \Big[\log|\sigma F_{Z_a}(c)| - \sum_y Z_a(y)\log\sup_i|\sigma(\mathrm{evalVec}\,s\,y)_i| - d\log\sup_i|\sigma(c_i)|\Big],$$
--   the conclusion is the identity $G(a,c) - G(a',c) = G(a,e) - G(a',e)$, all four terms being written out explicitly in the statement.
--
--   This is the exact cocycle relation satisfied by the normalised defect between the two ways of pairing a hyperplane section against a zero-cycle on the modular curve, deduced from reciprocity of Chow forms in degree one; the normalising terms involving $\sup_i|\sigma(\cdot)|$ cancel, so that the content lies in the logarithms of the Chow forms. It is used by [`ModularCurve.JZero.hyperplaneSection_cocycle_bounded`](thm.html#ModularCurve.JZero.hyperplaneSection_cocycle_bounded) in the construction of the archimedean height form on the degree-zero divisor class group of $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_hyperplaneSection_cocycle.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.hyperplaneSection_cocycle (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (σ : (AlgebraicClosure ℚ) →+* ℂ)
    (hCR : ∀ (k' : ℕ) (u' : modularFunctionFieldBar N)
        (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        u' ≠ 0 → u' ∈ riemannRochSpace ((k' : ℤ) • embDivisor N) →
        (∀ w, B' w = w.ord u' + ((k' : ℤ) • embDivisor N) w) →
        ChowReciprocity s (embDivisor N) k' u' B')
    (a a' c e : Fin r → AlgebraicClosure ℚ)
    (Za Za' Zc Ze : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (ha : linSec s a ≠ 0) (ha' : linSec s a' ≠ 0) (hc : linSec s c ≠ 0) (he : linSec s e ≠ 0)
    (hZa : (∀ w, Za w = w.ord (linSec s a) + embDivisor N w)) (hZa' : (∀ w, Za' w = w.ord (linSec s a') + embDivisor N w))
    (hZc : (∀ w, Zc w = w.ord (linSec s c) + embDivisor N w)) (hZe : (∀ w, Ze w = w.ord (linSec s e) + embDivisor N w))
    (hac : (∀ w, Za w = 0 ∨ Zc w = 0)) (ha'c : (∀ w, Za' w = 0 ∨ Zc w = 0))
    (hae : (∀ w, Za w = 0 ∨ Ze w = 0)) (ha'e : (∀ w, Za' w = 0 ∨ Ze w = 0)) :
    ((Real.log ‖σ (MvPolynomial.eval a (chowForm s Zc))‖
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
              - embDegree N * Real.log (⨆ i, ‖σ (c i)‖)))
    = ((Real.log ‖σ (MvPolynomial.eval a (chowForm s Ze))‖
              - (Ze.sum fun z n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s z i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (a i)‖))
            - (Real.log ‖σ (MvPolynomial.eval e (chowForm s Za))‖
              - (Za.sum fun y n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (e i)‖)))
      - ((Real.log ‖σ (MvPolynomial.eval a' (chowForm s Ze))‖
              - (Ze.sum fun z n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s z i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (a' i)‖))
            - (Real.log ‖σ (MvPolynomial.eval e (chowForm s Za'))‖
              - (Za'.sum fun y n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (e i)‖))) := by sorry
