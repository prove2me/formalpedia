-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_saturated_comparison
-- name    : MinimaxInterventions1429.Separable.saturated_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:08.58131+00:00
-- url     : https://prove2.me/theorems/e5935ac7-5f92-4f9f-ba74-114ec1d53182
-- title:
--   Lemma 3.3 — saturated comparison
-- statement:
--   Let $m,k\ge2$, $L\in[0,1]^{m\times k}$, $\alpha,\kappa\ge0$, integer $T\ge1$, and $\eta=2^{-T}$, $z=\alpha+2\kappa$, $H=2z+\eta$. Suppose $\widehat\omega\in[-1,1]^{m\times k}$, $\widehat\omega_{g1}=0$, and its entrywise error relative to $\omega_{gh}=L_{gh}-L_{g1}$ is at most $\kappa$. For distinct rows $g,r$ and an action $h$ with $d=\widehat\omega_{gh}-\widehat\omega_{rh}>4z$, put $u=\widehat\omega_{gh}$ and $v=\widehat\omega_{rh}$. For $t\in[-1,1]$, take $b_g=-t-d/2$, $b_r=0$, $b_{g'}=-4$ otherwise, $c_1=0$, $c_h=-(u+v)/2$, and $c_j=3$ off the pair. Then $B_{g'j}=b_{g'}+c_j$ belongs to $\mathcal S$, and every $\alpha$-optimal mixture satisfies
--
--   $$p_h\ge\tfrac12\Longrightarrow a_g-a_r\le t+2z,
--   \qquad p_h\le\tfrac12\Longrightarrow a_g-a_r\ge t-2z,
--   \quad a_g=L_{g1}.$$
--
--   The literal $T$-call search with slack $2z$ estimates $a_g-a_r$ within $H$, under accuracy of those realized calls alone. The result covers every $\kappa\ge0$ permitted by the stated separation and gives row-level comparisons at error independent of inverse separation.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
--   - encoding: adversarial bit answers accurate only along the realized calls → a finite bit-query program evaluated with an arbitrary history-dependent oracle and a witness for each recorded bit; reason: the program observes only bits and public queries; weak ties admit both bits and no common witness or numerical response is assumed
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Lemma 3.3, printed p.10 (PDF p.12)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem saturated_comparison {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (L w : Table m k) (hL : InCube L)
    (α κ : ℝ) (hα : 0 ≤ α) (hκ : 0 ≤ κ) (T : ℕ) (hT : 1 ≤ T)
    (hw : ∀ g h, -1 ≤ w g h ∧ w g h ≤ 1)
    (hw0 : ∀ g, w g 0 = 0) (herr : ∀ g h, |w g h - contrasts L g h| ≤ κ)
    (g r : Fin m) (hgr : g ≠ r) (h : Fin k)
    (hsep : 4 * effectiveTolerance α κ < w g h - w r h) :
    (∀ t : ℝ, -1 ≤ t → t ≤ 1 →
      Allowed (saturated w g r h t) ∧ ∀ p : Mixture k,
      Optimal (L + saturated w g r h t) α p →
        ((1 : ℝ) / 2 ≤ p.val h → L g 0 - L r 0 ≤ t + 2 * effectiveTolerance α κ) ∧
        (p.val h ≤ (1 : ℝ) / 2 → t - 2 * effectiveTolerance α κ ≤ L g 0 - L r 0)) ∧
    (levelSearch α κ T w g r h).maxQueries = T ∧
    (∀ O : BitOracle m k, ∀ hist : History m k,
      AccurateHistory L α (((levelSearch α κ T w g r h).run O hist).2.drop hist.length) →
      |((levelSearch α κ T w g r h).run O hist).1 - (L g 0 - L r 0)| ≤ edgeError α κ T)
      := by sorry

end MinimaxInterventions1429.Separable
