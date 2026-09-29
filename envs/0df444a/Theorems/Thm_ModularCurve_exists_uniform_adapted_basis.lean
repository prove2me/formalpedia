-- Prove2me | Theorems.Thm_ModularCurve_exists_uniform_adapted_basis
-- name    : ModularCurve.exists_uniform_adapted_basis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/b95263bf-b250-5719-a3f5-a507e0ca7262
-- title:
--   Uniform adapted bases with bounded chordal distortion at p∤ N
-- statement:
--   Let $N$ be a nonzero natural number, let $r$ be a natural number and let $s\colon \mathrm{Fin}\,r\to$ `modularFunctionFieldBar N` (the base change to $\overline{\mathbb Q}$ of the full level-$N$ modular function field inside Laurent series) satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space of the divisor `embDivisor N`. Let $p$ be a prime with $p\nmid N$. Then there is a natural number $B$ with the following property. For every valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, and every `ConstantReduction` datum $R$ from `modularFunctionFieldBar N` to `modularFunctionFieldFullC (ResidueField A) N` over $A$ — a valuation subring `R.integers` of the function field meeting $\overline{\mathbb Q}$ in $A$, a surjective residue map `R.residue` onto the reduced function field with kernel the maximal ideal and compatible with $A\to\mathrm{ResidueField}\,A$, a degree-preserving map `R.placeMap` on places compatible with orders of functions with nonzero residue, and a scaling property — such that $R$ is good (the reduced function field has the same genus) and `R.placeMap` satisfies `IsPlaceReductionModL A N`, there exists $t\colon \mathrm{Fin}\,r\to$ `modularFunctionFieldBar N` with `IsEmbBasis N t`, all $t_l\in$ `R.integers`, the residues `R.residue (t l)` linearly independent over $\mathrm{ResidueField}\,A$, and such that for every nonarchimedean absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit ball is exactly $A$, all places $P,Q$ of `modularFunctionFieldBar N` over $\overline{\mathbb Q}$ and all indices $c_P,c_Q$ with $P.\mathrm{ord}(t_j t_{c_P}^{-1})\ge 0$ and $Q.\mathrm{ord}(t_j t_{c_Q}^{-1})\ge 0$ for all $j$, if the vectors `evalVec s P` and `evalVec s Q` are non-proportional (some $2\times2$ minor is nonzero), then the chordal proximity $\mathrm{prox}_\mu(x,y)=\log\sup_i\mu(x_i)+\log\sup_j\mu(y_j)-\log\sup_{i,j}\mu(x_iy_j-x_jy_i)$ computed for the $s$-coordinate vectors at $P,Q$ and for the $t$-coordinates $j\mapsto P.\mathrm{evalAt}(t_jt_{c_P}^{-1})$, $j\mapsto Q.\mathrm{evalAt}(t_jt_{c_Q}^{-1})$ differ in absolute value by at most $B\cdot(-\log\mu(p))$.
--
--   This is the uniform form of the existence of a basis of the Riemann–Roch space of `embDivisor N` adapted to a good constant reduction of the function field of $X_0(N)$ at a prime $p\nmid N$: the point is that a single bound $B$, independent of the valuation subring $A$ above $p$ and of the reduction datum, controls the distortion of chordal proximity between the $s$- and $t$-coordinate models. It is used in the construction of uniform dual-graph coverings at primes not dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_uniform_adapted_basis.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_ReductionModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_uniform_adapted_basis (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ N) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ R : ConstantReduction A (modularFunctionFieldBar N)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      R.IsGood → IsPlaceReductionModL A N R.placeMap →
    ∃ t : Fin r → modularFunctionFieldBar N, IsEmbBasis N t ∧
      ∃ hint : ∀ l, t l ∈ R.integers,
        LinearIndependent (IsLocalRing.ResidueField A) (fun l => R.residue ⟨t l, hint l⟩) ∧
        ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
          (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
          ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ cP cQ : Fin r,
            (∀ j, 0 ≤ P.ord (t j * (t cP)⁻¹)) → (∀ j, 0 ≤ Q.ord (t j * (t cQ)⁻¹)) →
            (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
            |prox (μ : AlgebraicClosure ℚ → ℝ) (evalVec s P) (evalVec s Q)
                - prox (μ : AlgebraicClosure ℚ → ℝ) (fun j => P.evalAt (t j * (t cP)⁻¹))
                    (fun j => Q.evalAt (t j * (t cQ)⁻¹))|
              ≤ (B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
