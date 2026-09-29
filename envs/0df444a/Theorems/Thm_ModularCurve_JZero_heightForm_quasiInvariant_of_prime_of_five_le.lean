-- Prove2me | Theorems.Thm_ModularCurve_JZero_heightForm_quasiInvariant_of_prime_of_five_le
-- name    : ModularCurve.JZero.heightForm_quasiInvariant_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/44988ed4-3b07-58ec-ac37-40f4e5d814cf
-- title:
--   Quasi-invariance of the J₀(N) height form under linear equivalence
-- statement:
--   Let $N$ be a prime with $5 \le N$, let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$, and let $s = (s_0,\dots,s_{r-1})$ be a family in the function field $F =$ `modularFunctionFieldBar N` (the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$) which is an embedding basis in the sense of `IsEmbBasis`: $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space $\{f : v.\mathrm{adicValuation}\,f \le \exp(D v) \text{ for all places } v\}$ of the divisor `embDivisor N`. Then there is a real $c_0$ such that for every $n \in \mathbb{N}$ there is a real $C$ with the following property. Let $c$ be an element of `JZero N`, the degree-zero divisor class group $\mathrm{Pic}^0$ of $F$ over $\overline{\mathbb{Q}}$, fixed by the action of the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing $K$ pointwise, and let $D_1, D_2$ be divisors of $F$ (finitely supported $\mathbb{Z}$-valued functions on places) each of which represents $c$ in degree $n$ in the sense of `JZero.IsRepOf`: $D_i$ is effective, there is a degree-zero divisor $E_i$ with $E_i + n\cdot[\overline{\infty}] = D_i$, where $\overline{\infty}$ is the place `cuspInftyBar N`, the class of $E_i$ is $c$, and $D_i$ is invariant under $\mathrm{arithmeticGalois}$ applied to each $\sigma$ in the fixing subgroup of $K$. Then
--   $$Q_s(D_1) \le Q_s(D_2) + c_0\bigl(h_n(D_1) + h_n(D_2)\bigr) + C,$$
--   where $h_n(D) =$ `divNaiveHeight N K n D` is the logarithmic height of the vector `symVec N n D` when all its entries lie in $K$, and $0$ otherwise, and $Q_s(D) =$ `JZero.heightForm N s D` is the quadratic expression `heightFormAux` evaluated, with $\gamma$ the genus `genusFF` of $F$ over $\overline{\mathbb{Q}}$ and base place $\overline{\infty}$, at the divisor $D' = D.\mathrm{erase}\,\overline{\infty}$, namely
--   $$\Bigl(\gamma + \textstyle\sum_v D'(v) - 1\Bigr)\sum_v D'(v)\,\mathrm{baseHt}_s(\overline{\infty}, v) - \tfrac12\!\!\sum_{(v,w)\ \text{off-diagonal}}\!\! D'(v)D'(w)\,\mathrm{pairHt}_s(v,w) - (2 - 2\gamma)\sum_v \frac{D'(v)(D'(v)-1)}{2}\,\mathrm{baseHt}_s(\overline{\infty}, v).$$
--
--   This is the quasi-invariance, or quasi-parallelogram, step in the Weil-style construction of heights on the Jacobian $J_0(N)$: the height form attached to an embedding basis depends on the chosen effective representative of a class only up to an error which is linear in the naive heights of the representatives, with slope $c_0$ uniform in the degree $n$ (only the additive constant is allowed to depend on $n$). It is used in [`ModularCurve.JZero.naiveHeight_growth_of_prime_of_five_le`](thm.html#ModularCurve.JZero.naiveHeight_growth_of_prime_of_five_le), and rests on the bound [`ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le`](thm.html#ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le) for the pairing against principal divisors together with [`ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight`](thm.html#ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_heightForm_quasiInvariant_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.heightForm_quasiInvariant_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ n : ℕ, ∃ C : ℝ, ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D₁ D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      JZero.IsRepOf N K n c D₁ → JZero.IsRepOf N K n c D₂ →
      JZero.heightForm N s D₁ ≤ JZero.heightForm N s D₂
        + c₀ * (divNaiveHeight N K n D₁ + divNaiveHeight N K n D₂) + C := by sorry
