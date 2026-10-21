-- Prove2me | Theorems.Thm_NumInvQH_Oblique_theorem_4_3
-- name    : NumInvQH.Oblique.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:36.77973+00:00
-- url     : https://prove2.me/theorems/f9a5f433-ce54-481c-a33d-704cbd008400
-- title:
--   Theorem 4.3 — explicit oblique-projection formulas for the optimal adjustment $a$ and pure hedge $\xi$, pointwise in $\mathbb R^d$
-- statement:
--   Throughout, $X^{+}$ denotes the Moore–Penrose pseudoinverse of a real matrix $X$: the unique matrix satisfying $XX^{+}X=X$, $X^{+}XX^{+}=X^{+}$, $(XX^{+})^{\mathsf T}=XX^{+}$, $(X^{+}X)^{\mathsf T}=X^{+}X$ (the paper writes $X^{-1}$). $R(\cdot)$ is the column space and $N(\cdot)$ the null space of a matrix.
--
--   Fix the pointwise data of the hedging problem at one time and state: a matrix $C=\tilde c^{S\star}\in\mathbb R^{d\times d}$ that is symmetric positive semidefinite (the modified second characteristic of the price process $S$), vectors $b=b^{S\star}$, $s=S_-\neq0$ and $u=\tilde c^{SV\star}\in R(C)$ in $\mathbb R^d$, and a scalar $v=V_-$. Strategies $\vartheta$ are row vectors. Let
--
--   $$\Xi_a=\operatorname*{arg\,min}_{\vartheta s=-1}\{\vartheta C\vartheta^{\mathsf T}-2\vartheta b\},\qquad \Xi_\xi=\operatorname*{arg\,min}_{\vartheta s=v}\{\vartheta C\vartheta^{\mathsf T}-2\vartheta u\}$$
--
--   be the sets of all minimizers in (4.3) and (4.7), and put
--
--   $$m=I-\frac{ss^{\mathsf T}}{s^{\mathsf T}s},\quad p=(mCm)^{+},\quad a=b^{\mathsf T}p-\frac{s^{\mathsf T}}{s^{\mathsf T}s}(I-Cp),\quad \xi=u^{\mathsf T}p+v\,\frac{s^{\mathsf T}}{s^{\mathsf T}s}(I-Cp).$$
--
--   Then:
--
--   1. $\Xi_a$ is non-empty if and only if $b\in R(C)+R(s)$. In this case $\Xi_a=a+N(C)\cap N(s^{\mathsf T})$ and $a$ is the minimum-norm element of $\Xi_a$.
--   2. $\Xi_\xi=\xi+N(C)\cap N(s^{\mathsf T})$, and $\xi$ is the minimum-norm element of $\Xi_\xi$.
--   3. If $s\in R(C)$, then
--
--   $$a=b^{\mathsf T}C^{+}-\bigl(1+b^{\mathsf T}C^{+}s\bigr)\frac{s^{\mathsf T}C^{+}}{s^{\mathsf T}C^{+}s},\qquad \xi=u^{\mathsf T}C^{+}+\bigl(v-u^{\mathsf T}C^{+}s\bigr)\frac{s^{\mathsf T}C^{+}}{s^{\mathsf T}C^{+}s}.$$
--
--   4. If $s\notin R(C)$, let $\bar m=I-CC^{+}$, $\alpha=\dfrac{s^{\mathsf T}\bar m}{s^{\mathsf T}\bar ms}$ and $r=\alpha b$. Then
--
--   $$a=(b-rs)^{\mathsf T}C^{+}-\bigl(1+(b-rs)^{\mathsf T}C^{+}s\bigr)\alpha,\qquad \xi=u^{\mathsf T}C^{+}+\bigl(v-u^{\mathsf T}C^{+}s\bigr)\alpha,$$
--
--   and $\alpha s=1$, $\alpha C=0$.
--
--   In the paper, $a$ is the optimal adjustment process and $\xi$ the pure hedge coefficient of numeraire-invariant quadratic hedging (Theorem 4.1); the theorem expresses both through oblique projections and identifies the whole solution sets.
--
--   **Formalization Note** The semimartingale quantities are read pointwise, at a fixed $(\omega,t)$, as the finite-dimensional data above; the stochastic construction of Theorem 4.1 is not part of the statement. The hypothesis $s\neq0$ is implicit in the paper (there $S_-\neq0$ because $S$ admits a numeraire with positive value; without it the iff in (1) is false and $s^{\mathsf T}s=0$ is a denominator). The hypothesis $u\in R(C)$ is what "in the setting of Theorem 4.1" contributes to part (2), as the proof states; the milestone `range_fact_4_3` derives it from positive semidefiniteness of the joint characteristic. Of the last sentence of part (4), which interprets $\alpha$ as the instantaneously risk-free fully invested portfolio, only its algebraic content $\alpha s=1$ and $\alpha C=0$ is formalised. The four parts are the conjuncts of one statement, in order; $a$ and $\xi$ are local definitions (`let`). Every pseudoinverse is an explicit matrix argument together with the hypothesis that it satisfies the four Penrose equations (`LocalDistanceNetwork.IsMoorePenroseInverse`); since such a matrix exists and is unique, this is the same as using "the" pseudoinverse. Lean's matrix inverse `⁻¹` is never used for a matrix; it appears only for real scalars.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, p. 16, Theorem 4.3, eqs. (4.12)–(4.15)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Theorem 4.3, read pointwise in real finite dimensions: `C` is c̃^{S⋆}, `b` is b^{S⋆}, `s` is S₋,
`u` is c̃^{SV⋆} (c̃^{VS⋆} read as a row), `v` is V₋; `p` and `Cp` are the Moore–Penrose
pseudoinverses of `mCm` and `C`. Parts (1)–(4) are the conjuncts in order; the last two equalities
of part (4) are the algebraic content of "α is the instantaneously risk-free fully invested
portfolio" (αS₋ = 1, αc̃^{S⋆} = 0). -/
theorem theorem_4_3 {d : ℕ}
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (b s u : Fin d → ℝ) (v : ℝ) (hs : s ≠ 0)
    (hu : u ∈ LinearMap.range (Matrix.toLin' C))
    (p Cp : Matrix (Fin d) (Fin d) ℝ)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse
      ((1 - (s ⬝ᵥ s)⁻¹ • Matrix.vecMulVec s s) * C *
        (1 - (s ⬝ᵥ s)⁻¹ • Matrix.vecMulVec s s)) p)
    (hCp : LocalDistanceNetwork.IsMoorePenroseInverse C Cp) :
    let a := b ᵥ* p - (s ⬝ᵥ s)⁻¹ • (s ᵥ* (1 - C * p))
    let ξ := u ᵥ* p + (v * (s ⬝ᵥ s)⁻¹) • (s ᵥ* (1 - C * p))
    let Ξa := hyperArgmin C b s (-1)
    let Ξξ := hyperArgmin C u s v
    (Ξa.Nonempty ↔ b ∈ LinearMap.range (Matrix.toLin' C) ⊔ Submodule.span ℝ {s}) ∧
    (b ∈ LinearMap.range (Matrix.toLin' C) ⊔ Submodule.span ℝ {s} →
      Ξa = {x | ∃ z : Fin d → ℝ, C *ᵥ z = 0 ∧ s ⬝ᵥ z = 0 ∧ x = a + z} ∧
      IsMinNorm Ξa a) ∧
    (Ξξ = {x | ∃ z : Fin d → ℝ, C *ᵥ z = 0 ∧ s ⬝ᵥ z = 0 ∧ x = ξ + z} ∧
      IsMinNorm Ξξ ξ) ∧
    (s ∈ LinearMap.range (Matrix.toLin' C) →
      a = b ᵥ* Cp - ((1 + b ⬝ᵥ (Cp *ᵥ s)) / (s ⬝ᵥ (Cp *ᵥ s))) • (s ᵥ* Cp) ∧
      ξ = u ᵥ* Cp + ((v - u ⬝ᵥ (Cp *ᵥ s)) / (s ⬝ᵥ (Cp *ᵥ s))) • (s ᵥ* Cp)) ∧
    (s ∉ LinearMap.range (Matrix.toLin' C) →
      let mbar := 1 - C * Cp
      let α := (s ⬝ᵥ (mbar *ᵥ s))⁻¹ • (s ᵥ* mbar)
      let r := α ⬝ᵥ b
      a = (b - r • s) ᵥ* Cp - (1 + (b - r • s) ⬝ᵥ (Cp *ᵥ s)) • α ∧
      ξ = u ᵥ* Cp + (v - u ⬝ᵥ (Cp *ᵥ s)) • α ∧
      α ⬝ᵥ s = 1 ∧ α ᵥ* C = 0) := by sorry

end NumInvQH.Oblique
