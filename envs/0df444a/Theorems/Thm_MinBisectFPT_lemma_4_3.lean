-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_4_3
-- name    : MinBisectFPT.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:45.333315+00:00
-- url     : https://prove2.me/theorems/e6f68b7b-216f-4936-918d-11c44f895be2
-- title:
--   Lemma 4.3 — the table from the small configurations
-- statement:
--   Under the standing assumptions of §4, with $q=3k$:
--
--   1. In $R_t$,
--   $$F(\beta)=\sum_{i\le q,\ \ell\le|\alpha(t)|,\ j\le k,\ T\subseteq\sigma}N_i(T,\ell,j)\,x^iy^\ell z^ju^T,$$
--   where $N_i(T,\ell,j)$ is the number of configurations with $|X\cap\beta|=i$, pattern $T$, size $\ell$ and cut $j$, and $C^{\mathrm{sm}}_t(T,\ell,j)=\sum_{i\le q}N_i(T,\ell,j)$. So $C^{\mathrm{sm}}_t(T,\ell,j)$ is the sum of the coefficients of $x^iy^\ell z^ju^T$ in $F(\beta)$ over $0\le i\le q$.
--   2. If $|\beta|>2q$, then for all $T\subseteq\sigma$, $0\le\ell\le|\alpha(t)|$ and $0\le j\le k$,
--   $$C_t(T,\ell,j)=C^{\mathrm{sm}}_t(T,\ell,j)+C^{\mathrm{sm}}_t(\sigma\setminus T,|\alpha(t)|-\ell,j).$$
--
--   Differences from the source:
--   - reading: "the sum of the coefficients of $x^iy^\ell z^ju^T$ in $F(\beta)$" → an expansion of $F(\beta)$ in the monomials, with counts as coefficients; reason: the monomials are linearly independent (proved in the verification file), so the coefficients are these counts
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.3 and the paragraph before it, p.12

import Mathlib
import Definitions.Def_MinBisectFPT_NodeCtx

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 4.3**, with the paragraph above it. Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), p.12. The first clause says that the count with
`|X ∩ β| = i` is the coefficient of `x^i y^ℓ z^j u^T` in `F(β)` (`i ≤ q`, `j ≤ k`), and that
`C^sm` is the sum of those counts over `i ≤ q`; the second is the printed identity. -/
theorem lemma_4_3 {n : ℕ} (ctx : NodeCtx n) :
    (ctx.F ctx.q ctx.β = ∑ i ∈ Finset.range (ctx.q + 1), ∑ l ∈ Finset.range (ctx.α.card + 1),
      ∑ j ∈ Finset.range (ctx.k + 1), ∑ T ∈ ctx.σ.powerset,
        ((ctx.bagCount i T l j : ℕ) : ctx.Rt ctx.q) * ctx.monoT ctx.q i l j T) ∧
    (∀ (T : Finset (Fin n)) (l j : ℕ),
      ctx.smallCount T l j = ∑ i ∈ Finset.range (ctx.q + 1), ctx.bagCount i T l j) ∧
    (2 * ctx.q < ctx.β.card → ∀ T, T ⊆ ctx.σ → ∀ l, l ≤ ctx.α.card → ∀ j, j ≤ ctx.k →
      tableCount ctx.G ctx.D ctx.t T l j =
        ctx.smallCount T l j + ctx.smallCount (ctx.σ \ T) (ctx.α.card - l) j) := by sorry

end MinBisectFPT
