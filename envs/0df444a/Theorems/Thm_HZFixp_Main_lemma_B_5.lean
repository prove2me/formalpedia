-- Prove2me | Theorems.Thm_HZFixp_Main_lemma_B_5
-- name    : HZFixp.Main.lemma_B_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:54:01.572465+00:00
-- url     : https://prove2.me/theorems/f40d9e40-154b-4fb5-9dba-993ba6ad9b94
-- title:
--   Lemma B.5 — supporting prices with minimum zero; high goods cost more than one; full spending
-- statement:
--   Let $I$ be a Reciprocal VI instance and consider the HZ market of §3.4.1 built from it. For every HZ equilibrium $(X,p)$ of that market there are prices $p'$ such that $(X,p')$ is an HZ equilibrium with $\min_g p'_g = 0$, and at $p'$:
--   - every high good has price $>1$;
--   - every optimal bundle of every agent spends exactly one, $p'\cdot y = 1$;
--   - every optimum $(\gamma,\mu)$ of every agent's demand dual (50) has $\gamma>0$ and $\mu\ge0$;
--   - goods with identical utility columns have equal prices;
--   - if an agent consumes a good it values at zero ($X_{ag}>0$, $v_{ag}=0$), that good is free and every optimum of the agent's demand dual has $\mu=0$.
--
--   This is the first step of the proof of the market lemma (Lemma 3.11).
--
--   Differences from the source:
--   - encoding: the market's N agents and N goods in construction order → typed agents MAgent and goods MGood (node agents by node and copy, edge agents by edge; low goods by group and copy, high goods by node and copy, reference goods); equilibria are CardinalMatching.IsApproxHZ at ε = 0 over these types; reason: a relabelling of rows and columns; the lemmas do not depend on the order
--   - encoding: minimum price zero → minPrice p' = 0 (minPrice is 0 for a market without goods); reason: the only market without goods is the empty one (no nodes), where the claim is vacuous
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 58 (PDF 60), Lemma B.5

import Mathlib
import Definitions.Def_CardinalMatching_IsApproxHZ
import Definitions.Def_HZFixp_Main_ReciprocalVI
import Definitions.Def_HZFixp_Main_Market

namespace HZFixp.Main

/-- **Lemma B.5.** In the market of §3.4.1 built from a Reciprocal VI instance, every equilibrium
allocation admits supporting prices with minimum zero. At these prices, every high good costs more
than one, every optimal bundle spends one, and every demand-dual optimum has `γ > 0` and `µ ≥ 0`.
Goods with identical utility columns have equal prices, and an agent consumes a zero-utility good
only if that good is free and `µ = 0`. -/
theorem lemma_B_5 (I : RVIInst) (X : MAgent I.1 → MGood I.1 → ℝ) (p : MGood I.1 → ℝ)
    (hX : CardinalMatching.IsApproxHZ I.1.mUtil 0 X p) :
    ∃ p' : MGood I.1 → ℝ, CardinalMatching.IsApproxHZ I.1.mUtil 0 X p' ∧
      minPrice p' = 0 ∧
      (∀ g, I.1.IsHigh g → 1 < p' g) ∧
      (∀ a y, IsOptBundle (I.1.mUtil a) p' y → ∑ g, p' g * y g = 1) ∧
      (∀ a γ μ, IsOptDemandDual (I.1.mUtil a) p' γ μ → 0 < γ ∧ 0 ≤ μ) ∧
      (∀ g g', (∀ a, I.1.mUtil a g = I.1.mUtil a g') → p' g = p' g') ∧
      (∀ a g, 0 < X a g → I.1.mUtil a g = 0 →
        p' g = 0 ∧ ∀ γ μ, IsOptDemandDual (I.1.mUtil a) p' γ μ → μ = 0) := by sorry

end HZFixp.Main
