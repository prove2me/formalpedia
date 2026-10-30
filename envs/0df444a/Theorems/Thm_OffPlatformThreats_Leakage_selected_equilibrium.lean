-- Prove2me | Theorems.Thm_OffPlatformThreats_Leakage_selected_equilibrium
-- name    : OffPlatformThreats.Leakage.selected_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:41:57.809729+00:00
-- url     : https://prove2.me/theorems/2a5a8bcc-a330-48cc-ba8b-02199d21b639
-- title:
--   The selected participation equilibrium at a payout ratio $\omega$ (corrected: Definition 1 without its $N_p - 1$ clause)
-- statement:
--   Let $c, \phi, \mu > 0$, $R_o \ge 0$, $v > 0$, $K \ge 0$, $N \ge 1$ and $\omega \in [0, 1]$. There is exactly one selected equilibrium $(N_p, N_o)$, namely
--
--   $$N_p = \begin{cases} N, & \hat K \le \omega\, g_2(N, v),\\ 0, & \text{otherwise,}\end{cases} \qquad N_o = \begin{cases} N - N_p, & U_o \ge 0,\\ 0, & U_o < 0.\end{cases}$$
--
--   So either all providers are on the platform, or none is and they all go off the platform (if the off-platform utility is nonnegative) or all take their outside option. This is the form in which the proof of Proposition 2 uses Proposition 1.
--
--   Differences from the source:
--
--   - correction: Definition 1, first line: U_p(ω, N_p) ≥ (U_o)^+ and U_o < U_p(ω, N_p − 1), if N_p > 0 → U_p(ω, N_p) ≥ (U_o)^+, if N_p > 0; reason: with the second clause, (N, 0) is never an equilibrium at ω* = K̂/g2(N, v): for c = φ = µ = K = 1, v = 10, N = 2, Ro = 0 the only equilibrium at ω* ≈ 0.836 is (0, 2), leakage at Ro = 0 < a ≈ 6.80; the clause also contradicts Proposition 1, whose proof does not use it
--   - reading: providers settle on the equilibrium that corresponds to higher provider numbers (p. 16) → IsSelectedEq: a participation equilibrium whose N_p is maximal among all participation equilibria; reason: the rule is applied to the overlapping ranges of N_p in Proposition 1 (22) and in the proof of Proposition 2
--   - reading: U_p(ω, 0), used in Definition 1 at N_p = 0, is not defined ((10) assumes n_p ≥ 1 providers charging Q_p) → the optimal value of (9) with no provider in the queue, which is −K; reason: with n = 0 the demand (5) is 0, so every fee earns 0; also g2(0, v) := 0
--   - generalization: two provider types h, l with Λ > Nµ (1), K^h ≥ K^l, and φ = (1 + c_s²)/2 → one generic type (structure Market) with arbitrary φ > 0; Λ and the two-type order conditions do not appear; reason: every object of the statement involves only the shared parameters and those of type j, and (1) is used only to justify (5); the two-type statement is the conjunction over j = h, l
--   - generalization: K̂ = max{K, g2(1, v − Ro)} (21), U_o = g2(1, v − Ro) − K (20), with g2 defined on ℝ²₊ → (v − Ro)^+ in place of v − Ro; reason: agrees with the source whenever v ≥ Ro, the domain of g2; for v < Ro it is the off-platform revenue 0
--   - encoding: λ_p(C, q), λ_o(q) are the unique solutions of (5); U_p, U_o are the objectives of (9), (6) at an optimal fee → Classical choice of the unique solution of (5) (0 if none), and the supremum over fees ≥ 0 of the objectives of (9), (6); reason: Lemma 1 shows the solution exists and is unique, Lemma 2 that the suprema are attained; same values on every instance
--   - encoding: (5) off the platform: condition n_o ≥ 1 and v > q + Ro → condition q + Ro < v; reason: λ_o is evaluated only for a provider who is off the platform, so n_o ≥ 1 holds
--   - reading: the sign of K^j is not stated → 0 ≤ K; reason: K^j is an opportunity cost per unit time, and b^j contains √(K^j/(cφµ)), which is real only for K^j ≥ 0
--   - encoding: c (waiting cost) and µ (service rate) positive, implicit → 0 < c, 0 < µ; reason: the formulas divide by cφ and cφµ; excludes only undefined cases
--   - encoding: K̂/g2(1, v), K̂/g2(N, v) and Ro/g1(N, v), with g1, g2 defined on ℝ²₊ → 0 < v; reason: g1(n, 0) = g2(n, 0) = 0, so these quotients are undefined at v = 0; excludes only that case
--   - encoding: N^j providers of type j; (22) divides by g2(N^j, v^j) → N : ℕ with 1 ≤ N; reason: g2(0, v) divides by 0; excludes only the undefined case N = 0
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), selection rule p. 16 applied to Proposition 1; proof of Proposition 2, Appendix p. 4

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_Uo
import Definitions.Def_OffPlatformThreats_Leakage_IsSelectedEq
import Definitions.Def_OffPlatformThreats_Leakage_g2
import Definitions.Def_OffPlatformThreats_Leakage_Khat

namespace OffPlatformThreats.Leakage

/-- **The selected participation equilibrium.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), selection rule p. 16 (unnumbered)
applied to Proposition 1; proof of Proposition 2, Appendix p. 4.

Let `c, φ, µ > 0`, `Ro ≥ 0`, `v > 0`, `K ≥ 0`, `N ≥ 1` and `ω ∈ [0, 1]`. There is exactly one
selected equilibrium `(N_p, N_o)`: `N_p = N` and `N_o = 0` if `K̂ ≤ ω g2(N, v)`; otherwise
`N_p = 0`, with `N_o = N` if `U_o ≥ 0` and `N_o = 0` if `U_o < 0`. -/
theorem selected_equilibrium (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi)
    (hmu : 0 < m.mu) (hRo : 0 ≤ m.Ro) (hv : 0 < m.v) (hK : 0 ≤ m.K) (hN : 1 ≤ m.N)
    (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    (∃! p : ℕ × ℕ, IsSelectedEq m ω p.1 p.2) ∧
    ∀ np no : ℕ, IsSelectedEq m ω np no →
      np = (if Khat m ≤ ω * g2 m m.N m.v then m.N else 0) ∧
      no = (if 0 ≤ Uo m then m.N - np else 0) := by sorry

end OffPlatformThreats.Leakage
