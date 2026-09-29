-- Prove2me | Theorems.Thm_ModularCurve_JZero_heightForm_quasiInvariant_eps_of_prime_of_five_le
-- name    : ModularCurve.JZero.heightForm_quasiInvariant_eps_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/457b9a0f-bbc8-50a9-87c2-8b7995ed570e
-- title:
--   Quasi-invariance of the height form along a class, prime level ≥ 5
-- statement:
--   Let $N$ be a nonzero natural number that is prime with $N \ge 5$, let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$, and let $s : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N` be a family in the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ which is an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its range spans the Riemann–Roch space $\{f : v.\mathrm{adicValuation}\,f \le \exp(\mathrm{embDivisor}\,N\,v)\text{ for all places }v\}$ of the divisor `embDivisor N`. Then for every $\varepsilon_0 > 0$ and every $n : \mathbb{N}$ there is a real constant $C$ with the following property: for every class $c$ in the part of $\mathrm{Pic}^0$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ fixed by the subgroup of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing $K$ pointwise, and for any two divisors $D_1, D_2$ each of which represents $c$ at level $n$ — that is, each $D_i$ is effective, equals $E_i + n\cdot[\infty]$ for a degree-zero divisor $E_i$ with class $c$, where $[\infty]$ is the cusp place `cuspInftyBar N`, and is invariant under the arithmetic Galois action of every automorphism fixing $K$ — one has $$Q(D_1) \le Q(D_2) + \varepsilon_0\,(h_n(D_1) + h_n(D_2)) + C,$$ where $Q(D)$ is the height form `JZero.heightForm N s D`, the explicit quadratic expression in the local quantities $\mathrm{baseHt}$ and $\mathrm{pairHt}$ attached to $s$ and to the cusp, with $\gamma$ the genus of the function field, evaluated at $D$ with its coefficient at the cusp deleted, and $h_n(D) =$ `divNaiveHeight N K n D` is the logarithmic height over $K$ of the vector of symmetric coordinates $\mathrm{symVec}\,N\,n\,D$ (taken to be $0$ when these do not all lie in $K$). The constant $C$ may depend on $\varepsilon_0$ and $n$ but not on $c$, $D_1$, $D_2$.
--
--   This is the quasi-invariance of the height form along a linear-equivalence class, in the shape in which an arbitrarily small multiple of the naive heights of the two representatives is allowed as error, the order of quantifiers ($\varepsilon_0$ before $n$ before $C$) being the point. It is cited by [`ModularCurve.JZero.heightForm_lower_of_prime_of_five_le`](thm.html#ModularCurve.JZero.heightForm_lower_of_prime_of_five_le), which compares the height form with the naive height and must fix $\varepsilon_0$ only after its own constants; the proof invokes the bound of the point heights by the naive height, the fact that every place of the base-changed modular function field has degree one, and the estimate for the pairing against principal divisors at prime level at least five.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_heightForm_quasiInvariant_eps_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.heightForm_quasiInvariant_eps_of_prime_of_five_le (N : ℕ) [NeZero N]
    (hN : N.Prime) (hN5 : 5 ≤ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ n : ℕ, ∃ C : ℝ, ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D₁ D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      JZero.IsRepOf N K n c D₁ → JZero.IsRepOf N K n c D₂ →
      JZero.heightForm N s D₁ ≤ JZero.heightForm N s D₂
        + ε₀ * (divNaiveHeight N K n D₁ + divNaiveHeight N K n D₂) + C := by sorry
