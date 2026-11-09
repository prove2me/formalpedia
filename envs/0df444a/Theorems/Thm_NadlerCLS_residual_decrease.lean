-- Prove2me | Theorems.Thm_NadlerCLS_residual_decrease
-- name    : NadlerCLS.residual_decrease
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:01:19.104955+00:00
-- url     : https://prove2.me/theorems/26bce3b8-a00d-4077-97b4-fabff81ae9bb
-- title:
--   Residual decrease from the (N2) certificate
-- statement:
--   Let an instance of $\beta$-Projected-Nadler be given in the input format, with clipped $\Pi$, $d$, diagonal map $P$ and residual $r(x)=d(x,P(x))$, and let $x\in[0,1]^n$. Suppose the ordered triple $(x,P(x),x)$ is **not** an (N2) answer in the first orientation, i.e. with $u=\Pi(x,x)=P(x)$ and $v=\Pi(P(x),u)=P(P(x))$,
--   $$ d(u,v)\le k\,d(x,P(x))+\varepsilon_2 . $$
--   Then
--
--   1. $r(P(x))\le k\,r(x)+\varepsilon_2$;
--   2. $r(x)-r(P(x))\ge(1-k)\,r(x)-\varepsilon_2$;
--   3. if moreover $r(x)>\varepsilon_1$, then $r(x)-r(P(x))>0$.
--
--   This is the mechanism behind membership: away from (N1) answers the residual strictly decreases along $P$ unless an (N2) certificate appears.
--
--   Differences from the source:
--   - encoding: circuits $\Pi$, $d$ with the ranges $P(X)\subseteq X$, $d\in[0,D]$ → the clipped circuit values of `PNInstance`; reason: Remark C.7's enforced ranges; no change on in-range instances
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Section 3, "Residual decrease", pp.10–11

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_PNInstance

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Residual decrease** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points
for Set-Valued Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256
1fcc5a02…6dc485, Section 3, "Residual decrease", pp.10–11). Let `I` be a β-Projected-Nadler
instance in the input format and `x ∈ [0, 1]ⁿ`. If the ordered triple `(x, P(x), x)` is not an
(N2) answer in the first orientation (`u = Π(x, x) = P(x)`, `v = Π(P(x), u)`), then
`r(P(x)) ≤ k r(x) + ε₂`, hence `r(x) − r(P(x)) ≥ (1 − k) r(x) − ε₂`, and if moreover
`r(x) > ε₁` the decrease `r(x) − r(P(x))` is strictly positive.

**Formalization Note** Π and d are the clipped circuits of `PNInstance`. -/
theorem residual_decrease {n : ℕ} (I : PNInstance n) (hI : I.Valid) (x : Fin n → ℝ)
    (hx : InCube x)
    (hN2 : ¬ (I.dist (I.Pi x x) (I.Pi (I.P x) (I.Pi x x)) >
      (I.k : ℝ) * I.dist x (I.P x) + I.ε₂)) :
    I.r (I.P x) ≤ (I.k : ℝ) * I.r x + I.ε₂ ∧
    I.r x - I.r (I.P x) ≥ (1 - (I.k : ℝ)) * I.r x - I.ε₂ ∧
    ((I.ε₁ : ℝ) < I.r x → 0 < I.r x - I.r (I.P x)) := by sorry

end NadlerCLS
