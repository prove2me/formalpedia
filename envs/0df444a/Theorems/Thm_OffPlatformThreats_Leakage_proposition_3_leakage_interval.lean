-- Prove2me | Theorems.Thm_OffPlatformThreats_Leakage_proposition_3_leakage_interval
-- name    : OffPlatformThreats.Leakage.proposition_3_leakage_interval
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:44:22.531372+00:00
-- url     : https://prove2.me/theorems/a8a11f8b-7a3e-490b-9c26-fc143d924554
-- title:
--   Proposition 3: leakage occurs iff $a < R_o$ and $R_o$ is below $b$, or at $b$ with $K > 0$ (corrected: Definition 1 and right end-point)
-- statement:
--   Let $c, \phi, \mu > 0$, $R_o \ge 0$, $v \ge 0$, $K \ge 0$ and $N \ge 1$, and let $\omega^*$ be the payout ratio (23). Then a selected participation equilibrium exists at $\omega^*$, and for every selected participation equilibrium $(N_p, N_o)$ at $\omega^*$,
--
--   $$N_o > 0 \iff a < R_o \ \text{ and }\ \big(R_o < b \ \text{ or }\ (R_o = b \text{ and } K > 0)\big),$$
--
--   where $a$ and $b$ are the end-points of Proposition 3. Here demand is the solution of the customer equilibrium (5), utilities are the optimal values of the pricing problems (6) and (9), equilibria are those of Definition 1 (corrected) with the selection rule of p. 16.
--
--   In words: under the platform's payout ratio, some providers transact off the platform exactly when the counterparty risk lies in the leakage interval. Below $a$ the platform keeps all providers; above $b$ the off-platform option is unprofitable and providers take their outside option.
--
--   Differences from the source:
--
--   - correction: Definition 1, first line: U_p(ω, N_p) ≥ (U_o)^+ and U_o < U_p(ω, N_p − 1), if N_p > 0 → U_p(ω, N_p) ≥ (U_o)^+, if N_p > 0; reason: with the second clause, (N, 0) is never an equilibrium at ω* = K̂/g2(N, v): for c = φ = µ = K = 1, v = 10, N = 2, Ro = 0 the only equilibrium at ω* ≈ 0.836 is (0, 2), leakage at Ro = 0 < a ≈ 6.80; the clause also contradicts Proposition 1, whose proof does not use it
--   - correction: N_o(ω*) > 0 ⟺ Ro ∈ (a, b) → N_o > 0 ⟺ a < Ro ∧ (Ro < b ∨ (Ro = b ∧ 0 < K)); reason: at Ro = b, U_o = 0 and Definition 1 sends providers outside only if U_o < 0: for c = φ = µ = K = 1, v = 10, N = 2, Ro = 7 = b, (23) gives ω* = 0 and the only equilibrium is (0, 2), leakage at Ro = b; for K = 0, b = v and the open end-point is right
--   - reading: N_o(ω*), the number of off-platform providers in equilibrium at ω* → a selected equilibrium exists at ω*, and the equivalence holds for every selected equilibrium; reason: the notation presupposes that the equilibrium exists; stating existence and the claim for each selected equilibrium makes no choice
--   - reading: providers settle on the equilibrium that corresponds to higher provider numbers (p. 16) → IsSelectedEq: a participation equilibrium whose N_p is maximal among all participation equilibria; reason: the rule is applied to the overlapping ranges of N_p in Proposition 1 (22) and in the proof of Proposition 2
--   - reading: ω^{j*}, the optimal payout ratio of Proposition 2 → the closed form (23); reason: the proof of Proposition 3 uses (23); at Ro = a the platform's problem (15) has several maximizers
--   - reading: U_p(ω, 0), used in Definition 1 at N_p = 0, is not defined ((10) assumes n_p ≥ 1 providers charging Q_p) → the optimal value of (9) with no provider in the queue, which is −K; reason: with n = 0 the demand (5) is 0, so every fee earns 0; also g2(0, v) := 0
--   - generalization: two provider types h, l with Λ > Nµ (1), K^h ≥ K^l, and φ = (1 + c_s²)/2 → one generic type (structure Market) with arbitrary φ > 0; Λ and the two-type order conditions do not appear; reason: every object of the statement involves only the shared parameters and those of type j, and (1) is used only to justify (5); the two-type statement is the conjunction over j = h, l
--   - generalization: K̂ = max{K, g2(1, v − Ro)} (21), U_o = g2(1, v − Ro) − K (20), with g2 defined on ℝ²₊ → (v − Ro)^+ in place of v − Ro; reason: agrees with the source whenever v ≥ Ro, the domain of g2; for v < Ro it is the off-platform revenue 0
--   - encoding: λ_p(C, q), λ_o(q) are the unique solutions of (5); U_p, U_o are the objectives of (9), (6) at an optimal fee → Classical choice of the unique solution of (5) (0 if none), and the supremum over fees ≥ 0 of the objectives of (9), (6); reason: Lemma 1 shows the solution exists and is unique, Lemma 2 that the suprema are attained; same values on every instance
--   - encoding: (5) off the platform: condition n_o ≥ 1 and v > q + Ro → condition q + Ro < v; reason: λ_o is evaluated only for a provider who is off the platform, so n_o ≥ 1 holds
--   - encoding: c (waiting cost) and µ (service rate) positive, implicit → 0 < c, 0 < µ; reason: the formulas divide by cφ and cφµ; excludes only undefined cases
--   - encoding: N^j providers of type j; a^j contains (N^j − 1)/N^j → N : ℕ with 1 ≤ N, and N − 1 computed in ℝ; reason: a^j divides by N^j; excludes only the undefined case N = 0
--   - reading: the signs of v^j and K^j are not stated → 0 ≤ v and 0 ≤ K; reason: g1, g2 are defined on ℝ²₊ (p. 15), K^j is an opportunity cost per unit time, and b^j contains √(K^j/(cφµ)), which is real only for K^j ≥ 0
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), Proposition 3, p. 18, (25) p. 19; proof Appendix pp. 4–5

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_IsSelectedEq
import Definitions.Def_OffPlatformThreats_Leakage_omegaStar
import Definitions.Def_OffPlatformThreats_Leakage_aLeak
import Definitions.Def_OffPlatformThreats_Leakage_bLeak

namespace OffPlatformThreats.Leakage

/-- **Proposition 3 (Sufficient and Necessary Conditions for Platform Leakage), corrected.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), Proposition 3, p. 18, (25) p. 19;
proof Appendix pp. 4–5.

Let `c, φ, µ > 0`, `Ro ≥ 0`, `v ≥ 0`, `K ≥ 0` and `N ≥ 1`. At the payout ratio `ω^*` of (23),
a selected participation equilibrium exists, and in every selected equilibrium some providers
are off the platform (`N_o > 0`) iff `a < Ro` and either `Ro < b`, or `Ro = b` and `K > 0`.

**Formalization Note.** The printed (25) has `Ro ∈ (a, b)`; at `Ro = b` with `K > 0` the
off-platform utility is `0`, Definition 1 sends providers outside only if it is negative, and
every provider is off the platform (example `c = φ = µ = K = 1, v = 10, N = 2, Ro = 7 = b`).
Definition 1 is the corrected one (`IsParticipationEq`); demand is the solution of (5), the
utilities are the optimal values of (6) and (9), and `ω^*` is the closed form (23). -/
theorem proposition_3_leakage_interval (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi)
    (hmu : 0 < m.mu) (hRo : 0 ≤ m.Ro) (hv : 0 ≤ m.v) (hK : 0 ≤ m.K) (hN : 1 ≤ m.N) :
    (∃ np no : ℕ, IsSelectedEq m (omegaStar m) np no) ∧
    ∀ np no : ℕ, IsSelectedEq m (omegaStar m) np no →
      (0 < no ↔ aLeak m < m.Ro ∧ (m.Ro < bLeak m ∨ (m.Ro = bLeak m ∧ 0 < m.K))) := by sorry

end OffPlatformThreats.Leakage
