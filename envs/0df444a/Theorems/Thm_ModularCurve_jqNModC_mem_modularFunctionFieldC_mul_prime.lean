-- Prove2me | Theorems.Thm_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime
-- name    : ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/70fb938d-e81f-5282-94a5-913bfeb20f1e
-- title:
--   Descent: j(q^M)∈ K(j(q),j(q^{Mp}))
-- statement:
--   Let $K$ be a field, let $M$ be a nonzero natural number, let $p$ be a prime, and let $\zeta$ be a unit of $K$ whose underlying element is a primitive $(Mp)$-th root of unity in $K$. Write $j =$ `jqModC K` for the formal $j$-expansion in $K((q))$, namely $q^{-1}$ times the image in `LaurentSeries K` of the power series $E_4^3\cdot\eta^{-24}$ (`jNum`) under the coefficient map $\mathbb{Z}\to K$, and for $N\neq 0$ write `jqNModC K N` for its image under `qExpand K N`, the ring endomorphism of `LaurentSeries K` multiplying all exponents by $N$ (so $j(q^N)$). Assume, for every divisor $d$ of $M$, both that the degree $[\,K(j)(j(q^d)) : K(j)\,]$ equals $\psi(d) = \sum_{d'\mid d,\ d' \text{ squarefree}} d/d'$ (Dedekind's psi, `dedekindPsi`), and that `modularFunctionFieldC K d`, by definition the subfield of $K((q))$ generated over $K$ by $j(q)$ and $j(q^d)$, coincides with the subfield generated over $K$ by all $j(q^{d'})$ with $d'\mid d$, $d'\neq 0$. The conclusion is that $j(q^M)$ lies in `modularFunctionFieldC K (M * p)`, i.e. in the subfield of $K((q))$ generated over $K$ by the two elements $j(q)$ and $j(q^{Mp})$.
--
--   This is the downward (descent) step in the inductive study of the formal modular function fields $K(j(q),j(q^N))\subset K((q))$: the level-$M$ degree and generation data, together with the presence of a primitive $(Mp)$-th root of unity, force $j(q^M)$ to be the unique common root of $\Phi_p(j(q^{Mp}),Y)$ and of its own minimal polynomial over $K(j)$, hence to be rational over $K(j(q),j(q^{Mp}))$. It feeds into [`ModularCurve.package_of_socket`](thm.html#ModularCurve.package_of_socket), where the degree and generation statements are propagated to all levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean

import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime {K : Type*} [Field K]
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) :
    jqNModC K M ∈ modularFunctionFieldC K (M * p) := by sorry
