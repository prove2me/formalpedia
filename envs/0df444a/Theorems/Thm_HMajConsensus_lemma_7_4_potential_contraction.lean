-- Prove2me | Theorems.Thm_HMajConsensus_lemma_7_4_potential_contraction
-- name    : HMajConsensus.lemma_7_4_potential_contraction
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:15.005633+00:00
-- url     : https://prove2.me/theorems/c9b5264d-00e0-45bb-9b03-5a77dfa0f022
-- title:
--   Lemma 7.4 — potential contraction $E_t[\Phi_a(G_j(t+1))]\le(1-\rho/420)\Phi_a(G_j(t))$ (Items 1 and 2)
-- statement:
--   Consider $h$-Majority with $h\ge3$ on $n$ nodes and $2\le k\le n$ opinions, at an arbitrary round $t$. Let $\rho$ satisfy $0<\rho\le\frac1{80}\min\{h^2p_{\max}(t),1\}$ and let $a=n\rho/28$. With $G_j$, $\Phi_a$ and $I_t$ as in §7.1:
--
--   1. for every opinion $j\ne I_t$ with $p_j(t)\ge p_{\max}(t)/2$,
--   $$E_t\big[\Phi_a(G_j(t+1))\big]\ \le\ \Big(1-\frac{\rho}{420}\Big)\Phi_a(G_j(t));$$
--   2. for every pair of distinct opinions $i,j$ with $p_i(t)\ge p_{\max}(t)/2$ and $p_j(t)\ge p_{\max}(t)/2$,
--   $$E_t\big[\Phi_a(\max\{G_i(t+1),G_j(t+1)\})\big]\ \le\ \Big(1-\frac{\rho}{420}\Big)\Phi_a(\max\{G_i(t),G_j(t)\}).$$
--
--   This one-round contraction is the engine of symmetry breaking: among any two strong opinions, one becomes weak within $O(\log n/\rho)$ rounds (Lemma 7.2).
--
--   **Formalization Note** $E_t$ is the conditional expectation given the history up to round $t$; by the Markov property it is the integral against one step of the $h$-Majority kernel from the current configuration $C=C(t)$, so the lemma is stated for every configuration $C$. "$\rho$ does not depend on $t$" is then automatic. "$j\ne I_t$" says $j$ is not the smallest index of maximal density.
--
--   Differences from the source:
--   - encoding: E_t[·] = E[· | F_t] at an arbitrary round t of the process → the integral against step h C, for every configuration C; reason: Markov property: the conditional law of C(t+1) given F_t is step h (C(t)), and every configuration is a possible C(t); same instances
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Lemma 7.4 (Items 1 and 2), p.41 (G_j, Φ_a, p.41; I_t, p.40)

import Mathlib
import Definitions.Def_HMajConsensus_potential

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Lemma 7.4** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §7.1, p.41), both items: for any round, any `ρ` with
`0 < ρ ≤ (1/80) min{h²pmax, 1}` and `a = nρ/28`:
(1) for `j ≠ I_t` with `p_j ≥ pmax/2`, `E_t[Φ_a(G_j(t+1))] ≤ (1 − ρ/420) Φ_a(G_j(t))`;
(2) for distinct `i, j` with `p_i, p_j ≥ pmax/2`,
`E_t[Φ_a(max{G_i(t+1), G_j(t+1)})] ≤ (1 − ρ/420) Φ_a(max{G_i(t), G_j(t)})`.

**Formalization Note** `E_t` is the one-step expectation from the current configuration `C`
under the kernel `step h` (Markov property), so the statement is for every configuration `C`;
"`ρ` does not depend on `t`" is automatic. `j ≠ I_t` is `¬ IsTopIdx C j`. -/
theorem lemma_7_4_potential_contraction (n k h : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (hh : 3 ≤ h)
    (C : Config n k) (ρ : ℝ) (hρ : 0 < ρ) (hρle : ρ ≤ (1 / 80) * min ((h : ℝ) ^ 2 * pmax C) 1) :
    (∀ j : Fin k, ¬ IsTopIdx C j → pmax C / 2 ≤ density C j →
      ∫ C', phiA (n * ρ / 28) (potG C' j) ∂(step h C) ≤
        (1 - ρ / 420) * phiA (n * ρ / 28) (potG C j)) ∧
    (∀ i j : Fin k, i ≠ j → pmax C / 2 ≤ density C i → pmax C / 2 ≤ density C j →
      ∫ C', phiA (n * ρ / 28) (max (potG C' i) (potG C' j)) ∂(step h C) ≤
        (1 - ρ / 420) * phiA (n * ρ / 28) (max (potG C i) (potG C j))) := by sorry

end HMajConsensus
