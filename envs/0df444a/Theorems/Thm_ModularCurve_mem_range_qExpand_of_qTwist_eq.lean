-- Prove2me | Theorems.Thm_ModularCurve_mem_range_qExpand_of_qTwist_eq
-- name    : ModularCurve.mem_range_qExpand_of_qTwist_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/7fedb95c-f8b8-58c3-b4bc-f9bacad7fd66
-- title:
--   Laurent series fixed by q↦ζ q lie in K((qⁿ))
-- statement:
--   Let $K$ be a field, let $n$ be a nonzero natural number, and let $\zeta$ be a unit of $K$ whose underlying element is a primitive $n$-th root of unity in $K$ (in the sense of Mathlib's `IsPrimitiveRoot`). Let $f$ be a formal Laurent series over $K$, i.e. an element of `LaurentSeries K` = `HahnSeries ℤ K`, a function $k\mapsto f.\mathrm{coeff}\,k$ on $\mathbb{Z}$ whose support is partially well ordered, hence bounded below. Assume $f$ is fixed by the twist by $\zeta$: [`ModularCurve.qTwist ζ`](def/ModularCurve_PhiGen.html#L35) is the ring endomorphism of `LaurentSeries K` sending $f$ to the series with $k$-th coefficient $\zeta^{k} f.\mathrm{coeff}\,k$ (integer powers of the unit $\zeta$), the substitution $q\mapsto\zeta q$, and the hypothesis is `qTwist ζ f = f`. The conclusion is that $f$ belongs to the set-theoretic range of the ring homomorphism [`ModularCurve.qExpand K n`](def/ModularCurve_X0.html#L25), which is the Hahn-series embedding along the order-preserving injective additive map $m\mapsto n\,m$ of $\mathbb{Z}$, i.e. the substitution $q\mapsto q^{n}$: thus $f=g(q^{n})$ for some Laurent series $g$ over $K$. Only membership in the range is asserted; no preimage is named, and $n$ is not assumed prime.
--
--   This is the coefficientwise form of the standard observation that a $q$-expansion invariant under $q\mapsto\zeta q$ for a primitive $n$-th root of unity $\zeta$ is a series in $q^{n}$, the algebraic mechanism behind passing between expansions at the cusp in the variable $q$ and in $q^{N}$. It is used in the treatment of the modular curve $X_0(N)$, for instance in the integrality statements for $j(q)$ and $j(q^{N})$ over $\Gamma_0(N)$-invariant expansions, in the relations satisfied by modular units, and in the identification of the Fricke involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_range_qExpand_of_qTwist_eq.lean

import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.mem_range_qExpand_of_qTwist_eq {K : Type*} [Field K] (n : ℕ) [NeZero n] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) n) (f : LaurentSeries K) (h : ModularCurve.qTwist ζ f = f) : f ∈ Set.range (ModularCurve.qExpand K n) := by sorry
