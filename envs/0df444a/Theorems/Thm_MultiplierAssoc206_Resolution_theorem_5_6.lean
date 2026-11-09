-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_theorem_5_6
-- name    : MultiplierAssoc206.Resolution.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:12:16.504356+00:00
-- url     : https://prove2.me/theorems/ce814695-1371-4f1e-ac8e-7009da5be584
-- title:
--   The star-local extension $\mathsf{SPM}(H)$ requires refutations of size $2^{\Omega(m)}$
-- statement:
--   Let $\Delta\in\mathbb N$, $\Gamma\ge1$ and $\varepsilon>0$. There are $c>0$ and $m_0$ such that for every $m\ge m_0$ and every bipartite graph $H=(U,V,E)$ with $|U|=m+1$, $|V|=m$, maximum degree at most $\Delta$, which is an $(\varepsilon m,\Gamma)$-boundary expander and has a matching covering $V$,
--   $$\mathrm{size}_{\mathrm{Res}}\big(\mathsf{SPM}(H)\big)\ \ge\ 2^{cm}.$$
--   In particular this holds for the graphs of Theorem 5.4.
--
--   This is the hard formula from which the associativity lower bound is obtained by reduction.
--
--   Differences from the source:
--   - reading: Let H be a bipartite expander given by Theorem 5.4 → for all Δ, Γ ≥ 1, ε > 0 and every graph with |U| = m+1, |V| = m, maximum degree ≤ Δ, (εm, Γ)-boundary expansion and a matching covering V; reason: the stronger reading of 'given by Theorem 5.4', which specializes to the graphs that theorem provides; the proof uses only these properties
--   - encoding: size 2^{Ω(m)} → there are c > 0 and m₀, depending on Δ, Γ, ε only, with size ≥ 2^{cm} for m ≥ m₀; U and V arbitrary finite types; reason: explicit form of the asymptotic notation
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.10 (printed p.9), Theorem 5.6

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Graph

namespace MultiplierAssoc206.Resolution

/-- Theorem 5.6 (The star-local extension remains hard), PDF p.10 (printed p.9), for every
graph with the properties that Theorem 5.4 provides, with the constants `Δ, Γ, ε` arbitrary. -/
theorem theorem_5_6 (Δ : ℕ) (Γ ε : ℝ) (hΓ : 1 ≤ Γ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ (U V : Type) [Fintype U] [Fintype V], Fintype.card U = m + 1 → Fintype.card V = m →
      ∀ E : Finset (U × V), MaxDegLE E Δ → IsBoundaryExpander E (ε * m) Γ →
        HasMatchingCoveringV E → (2 : ℝ) ^ (c * m) ≤ (sizeRes (SPM E) : ℝ) := by sorry

end MultiplierAssoc206.Resolution
