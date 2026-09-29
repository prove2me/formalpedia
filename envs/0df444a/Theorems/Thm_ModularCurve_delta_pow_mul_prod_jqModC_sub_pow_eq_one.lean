-- Prove2me | Theorems.Thm_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one
-- name    : ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/23130db3-e879-5840-92f7-d7a103af64e5
-- title:
--   Kronecker congruence: Δ̄^{q-1} times the supersingular product is 1
-- statement:
--   Let $q$ be a prime with $q \ge 5$ and let $k$ be an algebraically closed field of characteristic $q$ (with decidable equality). Let $S_0$ be a finite subset of $k$ whose elements are exactly the members of `ssJSet q k`, that is, those $j \in k$ such that every Weierstrass curve $W$ over $k$ which is elliptic and has $W.j = j$ has no nonzero point $P$ of its affine model with $q \cdot P = 0$. Work in the Laurent series ring over $k$. Write $\bar\Delta$ for the image of the power series $X \cdot (\prod_{n \ge 1}(1 - X^{n}))^{24}$, reduced from $\mathbb{Z}$ to $k$, and let `jqModC k` be the Laurent series $\mathfrak q^{-1}$ times the reduction to $k$ of `jNum` $= E_4^3 \cdot$ `dedekindEtaUnitInv`. Then
--   $$\bar\Delta^{\,q-1} \cdot \prod_{a \in S_0} \bigl(\mathrm{jqModC}\,k - a\bigr)^{12 / e_a} = 1,$$
--   where $a$ is viewed as a constant Laurent series and $e_a =$ `jWidth a` is $3$ for $a = 0$, $2$ for $a = 1728$ and $1$ otherwise, so that the exponents $12/e_a$ are $4$, $6$ and $12$ respectively.
--
--   This is the Kronecker-type congruence identifying the reduction modulo $q$ of the modular unit $\Delta(\mathfrak q)^{1-q}$, along the component of $X_0(q)$ modulo $q$ through the cusp $\infty$, with the supersingular polynomial weighted by the automorphism widths at $j = 0$ and $j = 1728$; the total degree $q-1$ of the right-hand product reflects the Eichler–Deuring mass formula. It underlies the study of place specialisations and level-one prolongations on $X_0(q)$ in characteristic $q$, where it is used to control the residues of the modular unit series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve

theorem ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit)) ^ (q - 1) *
        ∏ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ (12 / jWidth a) = 1 := by sorry
