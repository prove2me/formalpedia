-- Prove2me | Theorems.Thm_NoRegretLastIterate_competitive_unique_ne_ce
-- name    : NoRegretLastIterate.competitive_unique_ne_ce
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:18.995308+00:00
-- url     : https://prove2.me/theorems/686fc37b-2783-4d25-9c89-05db0159db1a
-- title:
--   p.8 — a competitive game has a unique, completely mixed NE, and $p^*\times q^*$ is its unique correlated equilibrium
-- statement:
--   Let $(G,H)$ be a competitive $2\times2$ game (condition (a) or (b) of Definition 2.6). Then there are $p^*,q^*\in(0,1)$ such that
--
--   1. $(p,q)$ is a Nash equilibrium in mixed strategies if and only if $(p,q)=(p^*,q^*)$; and
--   2. a joint distribution $\mu$ on $\{0,1\}^2$ is a correlated equilibrium if and only if $\mu=p^*\times q^*$.
--
--   The paper states this after Definition 2.6 ("competitive games have a unique NE $(p^*,q^*)$ which is also its unique correlated equilibrium") together with the characterization of p.7 that the Nash equilibria of competitive games are completely mixed. Every later statement refers to this unique interior equilibrium.
--
--   **Formalization Note** A correlated equilibrium is the published `CalibratedCE.Convergence.IsCE` (payoff convention, no gain from any deviation map applied to one's recommendation).
--
--   Differences from the source:
--   - reading: "competitive games have a unique NE (p∗, q∗) which is also its unique correlated equilibrium" → the unique correlated equilibrium is the product distribution p∗ × q∗; reason: a Nash equilibrium is a correlated equilibrium through its product distribution; that is the only sense in which a NE "is" a CE
--   - generalization: p.8 sentence (uniqueness only) → adds the conjunct p∗, q∗ ∈ (0, 1); reason: this is the source's p.7 statement that the NE of a competitive game are completely mixed; dropping the conjunct gives the p.8 sentence
--   - encoding: (p∗, q∗) a Nash equilibrium in mixed strategies; actions 0, 1 → published RankOneBimatrix.BinSearch.IsNE on the probability vectors (1 − p, p), (1 − q, q); actions Fin 2; reason: Lean convention and published vocabulary; same instances
--   - encoding: correlated equilibrium of a 2 × 2 game → published CalibratedCE.Convergence.IsCE with deviation maps Φ : Fin 2 → Fin 2; reason: equivalent to the per-recommendation swap inequalities; published vocabulary
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, p.8 (after Definition 2.6), with p.7 (NE of competitive games completely mixed)

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_NoRegretLastIterate_Game

namespace NoRegretLastIterate

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, p.8 (after Definition 2.6): "competitive games
have a unique NE (p∗, q∗) which is also its unique correlated equilibrium", with p.7: the NE of a
competitive game are completely mixed. For every competitive `2 × 2` game `(G, H)` there are
`p∗, q∗ ∈ (0, 1)` such that `(p, q)` is a Nash equilibrium iff `(p, q) = (p∗, q∗)`, and a joint
distribution `D` on `{0, 1}²` is a correlated equilibrium iff `D = p∗ × q∗`.

**Formalization Note** Nash equilibrium is the published `RankOneBimatrix.BinSearch.IsNE` on the
probability vectors `(1 − p, p)`, `(1 − q, q)` (which forces `p, q ∈ [0, 1]`); correlated
equilibrium is the published `CalibratedCE.Convergence.IsCE` (payoff convention, deviation maps),
which includes that `D` is a joint distribution. -/
theorem competitive_unique_ne_ce {G H : Matrix (Fin 2) (Fin 2) ℝ} (hcomp : IsCompetitive G H) :
    ∃ p q : ℝ, p ∈ Set.Ioo (0 : ℝ) 1 ∧ q ∈ Set.Ioo (0 : ℝ) 1 ∧
      (∀ p' q' : ℝ, RankOneBimatrix.BinSearch.IsNE G H (mix p') (mix q') ↔ p' = p ∧ q' = q) ∧
      (∀ D : Fin 2 → Fin 2 → ℝ, CalibratedCE.Convergence.IsCE G H D ↔ D = prodDist p q) := by sorry

end NoRegretLastIterate
