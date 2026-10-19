-- Prove2me | Theorems.Thm_MarketplaceLeakage_Parity_proposition_4
-- name    : MarketplaceLeakage.Parity.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:22.172981+00:00
-- url     : https://prove2.me/theorems/d1ec18b6-7a9b-412e-8cc4-35a0fe9d4b6a
-- title:
--   Proposition 4, p. 23 — the marketplace prefers not to impose a price-parity clause iff q < 1/2 and μ > (v − c)/2; otherwise it prefers to impose one
-- statement:
--   Consider the marketplace-leakage game with uncertain switching costs: with probability $q$ buyers' switching costs are uniform on $[0,\mu]$, i.e. $G(s)=s/\mu$ for $s\in[0,\mu]$ (baseline state), and with probability $1-q$ they are infinite (no-switching state). The seller knows the state; the marketplace does not when it sets its per-transaction fee. Let $c<v$, $\mu>0$ and $0<q\le 1$.
--
--   Let $\Pi^*_{PPC}$ be the marketplace's optimal expected profit when it imposes a price-parity clause (the seller must set $p_d\ge p_m$ or be delisted), and $\Pi^*$ its optimal expected profit without one. Both optima exist, and:
--   1. the marketplace strictly prefers not to impose a PPC, $\Pi^*>\Pi^*_{PPC}$, if and only if
--   $$q<\frac12\quad\text{and}\quad \mu>\frac{v-c}{2};$$
--   2. otherwise it prefers to impose a PPC: $\Pi^*_{PPC}\ge\Pi^*$.
--
--   A price-parity clause eliminates leakage but forces the seller to choose between participating and delisting; the proposition says this cost dominates exactly when the baseline state is unlikely and switching costs in it are high.
--
--   **Formalization Note.** $\Pi^*_{PPC}$ and $\Pi^*$ are the `IsPPCValue` and `IsNoPPCValue` predicates of the setting file (attained maxima over the game's choices), and the theorem asserts that both exist and that the comparison holds for any values satisfying them. "Prefers to impose" is weak because there are ties: for $q<1/2$ and $\mu\le (v-c)/2$ the two values coincide. The hypothesis $q>0$ is added: at $q=0$ both values equal $v-c$ and part 1 fails. $q=1$ (no uncertainty) is allowed.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 23, Proposition 4 (proof: §8.5, pp. 39–40)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Parity_Setting

namespace MarketplaceLeakage.Parity

theorem proposition_4 (v c μ q : ℝ) (hvc : c < v) (hμ : 0 < μ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∃ V, IsPPCValue v c μ q V) ∧ (∃ W, IsNoPPCValue v c μ q W) ∧
    ∀ V W, IsPPCValue v c μ q V → IsNoPPCValue v c μ q W →
      ((V < W ↔ (q < 1 / 2 ∧ (v - c) / 2 < μ)) ∧
       (¬ (q < 1 / 2 ∧ (v - c) / 2 < μ) → W ≤ V)) := by sorry

end MarketplaceLeakage.Parity
