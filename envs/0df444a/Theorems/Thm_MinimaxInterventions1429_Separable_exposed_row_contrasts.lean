-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_exposed_row_contrasts
-- name    : MinimaxInterventions1429.Separable.exposed_row_contrasts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:05.847212+00:00
-- url     : https://prove2.me/theorems/cfa22d80-f13f-4c70-884a-c662fd3827a5
-- title:
--   Lemma 3.2 — exposed-row contrasts
-- statement:
--   Let $m,k\ge2$, $L\in[0,1]^{m\times k}$, $\alpha\ge0$, and integer $T\ge1$. For a row $g$, an action $h\ne1$, and $t\in[-1,1]$, define $b_g=0$, $b_r=-3$ for $r\ne g$, $c_1=t$, $c_h=0$, and $c_j=3$ off the pair. The surcharge $B_{rj}=b_r+c_j$ is separable with max-entry norm at most $5$. Writing $\omega_{gh}=L_{gh}-L_{g1}$, every $\alpha$-optimal mixture for $L+B$ obeys
--
--   $$p_h\ge\tfrac12\Longrightarrow\omega_{gh}\le t+2\alpha,
--   \qquad p_h\le\tfrac12\Longrightarrow\omega_{gh}\ge t-2\alpha.$$
--
--   Consequently the literal $T$-call contrast search with slack $2\alpha$ returns $\widehat\omega_{gh}\in[-1,1]$ with $|\widehat\omega_{gh}-\omega_{gh}|\le2\alpha+2^{-T}$. Calls can use arbitrary history-dependent bit choices with independently witnessing mixtures; only the calls made in this search must be accurate. The result identifies each exposed row's action contrasts without assuming its level is known.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
--   - encoding: adversarial bit answers accurate only along the realized calls → a finite bit-query program evaluated with an arbitrary history-dependent oracle and a witness for each recorded bit; reason: the program observes only bits and public queries; weak ties admit both bits and no common witness or numerical response is assumed
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Lemma 3.2, printed p.10 (PDF p.12)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem exposed_row_contrasts {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (L : Table m k) (hL : InCube L)
    (α : ℝ) (hα : 0 ≤ α) (T : ℕ) (hT : 1 ≤ T)
    (g : Fin m) (h : Fin k) (hh : h ≠ 0) :
    (∀ t : ℝ, -1 ≤ t → t ≤ 1 →
      Allowed (exposed g h t) ∧ ∀ p : Mixture k, Optimal (L + exposed g h t) α p →
        ((1 : ℝ) / 2 ≤ p.val h → contrasts L g h ≤ t + 2 * α) ∧
        (p.val h ≤ (1 : ℝ) / 2 → t - 2 * α ≤ contrasts L g h)) ∧
    (contrastSearch α T g h).maxQueries = T ∧
    (∀ O : BitOracle m k, ∀ hist : History m k,
      AccurateHistory L α (((contrastSearch α T g h).run O hist).2.drop hist.length) →
      let x := ((contrastSearch α T g h).run O hist).1
      (-1 ≤ x ∧ x ≤ 1 ∧ |x - contrasts L g h| ≤ 2 * α + eta T)) := by sorry

end MinimaxInterventions1429.Separable
